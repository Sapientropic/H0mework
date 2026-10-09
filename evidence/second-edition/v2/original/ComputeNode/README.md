# ComputeNode：把重型计算放到 PC 计算节点

Mac 产出彼此独立的计算单元 → PC（luciano-pc，WSL）按内存感知调度执行 → Mac 校验后收回。
luciano-pc 是仓库的**通用计算节点**，Mac 上的重型计算默认经本目录接入。从 J Coulomb 残差认证的实战中提炼
（`Lean/scratch/PcNode` 是它的首个实例，2026-10-06 已完成）。
协议与崩溃安全细节见 [ARCHITECTURE.md](ARCHITECTURE.md)，节点机器事实与装机见 [PC_SETUP.md](PC_SETUP.md)。
可用 `$compute-node` 调用[技能入口](../.agents/skills/compute-node/SKILL.md)，沿用本目录的实现与操作规范。

## 什么时候用

适合：能切成**彼此独立**的单元、单元 ≥10 s、单块内存 ≤20 GB 左右、结果可在 Mac 上按哈希核对。

- Lean：大批 `decide +kernel` 证书模块、生成式证书行/块、任何"给一组模块编出 .olean"的活；
- 命令：Python/Rust 数值扫描、SAT 实例批、参数网格；多核用 `slots`、大内存用 `mem_gb`、GPU（4090，24 GB）用 `gpu` 申报。

不适合：强依赖链（模块批内依赖会按轮次放行，但链很长时没有并行收益）、交互式证明开发、依赖 Mac 专属工具的任务。

## 上手

配置：`ComputeNode/pcnode.json`（git 忽略；由 `pcnode.example.json` 复制）。`remote_home` 是节点守护进程的家
（`~/pcnode`，内含内容寻址闭包库 `cas/`），`remote_lib` 是旧版共享库（`~/pcnode/lib`，已硬链接收编进 `cas/`），`githash` 必须与
`Lean/lean-toolchain` 的编译器一致。state 目录放在 `ComputeNode/state/<负载名>`（git 忽略，**不要放 /tmp**），
同级的 `cas-index.json` 是所有负载共享的节点 blob 索引。

Lean 模块批（依赖先 `lake build`；产物进 `--cache`，在 Mac 上把它加到 `LEAN_PATH` 最前即可 import）：

```bash
python3 ComputeNode/mac/lean_modules.py --config ComputeNode/pcnode.json --state ComputeNode/state/my-batch \
  --lean-root Lean --cache ComputeNode/state/my-batch/cache --modules-file modules.txt --until-done
```

命令批（单元写成 JSON lines，格式见 `mac/cmd_batch.py` 文首）：

```bash
python3 ComputeNode/mac/cmd_batch.py --config ComputeNode/pcnode.json --state ComputeNode/state/sweep \
  --units units.jsonl --base path/to/project --results ComputeNode/state/sweep/results --until-done
```

长跑用 `start.sh` 挂到守护脚本下（崩溃自动重启、改代码自动重载、跑完自行退出；`touch <state>/STOP` 停止，日志 `<state>/loop.log`）：

```bash
ComputeNode/mac/start.sh ComputeNode/state/my-batch python3 ComputeNode/mac/lean_modules.py --state ComputeNode/state/my-batch ...
```

Python 命令单元先把 uv 项目的锁定环境镜像到节点（按 `uv.lock` 原样安装，解释器版本跟 Mac 的 `.venv` 一致；项目元数据、锁与版本不变且解释器存在则跳过），
单元里用 `${PCNODE_ENVS}/<名>/.venv/bin/python`：

```bash
python3 ComputeNode/mac/node_env.py --config ComputeNode/pcnode.json --project Biomedical/runtime/calculations/<项目> --name <名>
```

看进度（节点状态与各负载份额、各负载进度、近一小时速率与 ETA、失败）：

```bash
python3 ComputeNode/mac/status.py --config ComputeNode/pcnode.json
```

撤回一个负载已投出的单元（先停它的 Mac 循环，再让节点给排队单元写 −15 收据、杀掉在跑的；别的负载不受影响）：

```bash
python3 ComputeNode/mac/cancel.py --config ComputeNode/pcnode.json --state ComputeNode/state/<负载>
```

## 多线程共用

节点是所有线程共享的，一个守护进程统一调度：

- **一个任务一个 state，一个名字**：负载名（`--name`，CLI 默认取 state 目录名）就是节点上的公平份额桶；
  每个 Mac 循环只按**自己**在节点排队的单元数补货，大批次不会挡住别人投递。
- **公平与优先级**：同一优先级里，空出的槽位给当前占得最少的负载；`--priority` 是严格分层，默认 0，
  正数只在用户要求加急时用，负数表示后台（只在没人排队时跑）。
- **没有抢占**：公平只在接纳时生效，单元尽量切到 ≤30–60 分钟；几小时的单元会让后来者等它跑完。
- **如实申报资源**：`slots` = 实际用的核数（同时在 `env` 里设 `OMP_NUM_THREADS` 等），`mem_gb` = 预期峰值（接纳时预留），
  `gpu: 1` = 要 4090；没申报 `gpu` 的单元看不到 GPU，env override 也不能打开；非法申报只让本单元失败。
- **冻结按资源分别计账**：冻结释放 CPU，继续保留内存和 GPU；重任务被冻结不会挡住能放下的轻任务，内存刹车仍停接。
  `status.py` 会显示清醒 slots、内存预留及等待原因。
- **环境名绑定版本**：Python 环境成功镜像后不原地改写；换依赖或重建用新 `--name`（建议项目名加锁哈希），避免影响其他负载。
- **闭包互不干扰**：节点闭包库按内容寻址，每个 job 只看到自己点名的版本；同一文件全节点只传一次、只存一份。
  命令单元的大输入可写进 `shared`，跨 job 去重、出现在 `${PCNODE_LIB}` 下。
- **新负载先试探**：没申报 `mem_gb` 的负载在攒够 4 个完成样本前只跑一个单元（或 2 slots），之后才按份额铺开；
  知道峰值就申报 `mem_gb`，可跳过试探。
- **持久工作区自己清**：跨单元或重跑要保留的检查点放 `${PCNODE_WORK}`（`~/pcnode/workloads/<负载名>`），不回传、节点不清理；
  负载完结后由其线程删除（2026-10-07 c14 的 CCSD(T) 检查点已占 70 GB）。
- **全局开关要协调**：`control.json`/`setctl.py`、`bench.py`（要求节点空闲）影响所有人，只在用户同意或节点空闲时做。
  `node/*.py` 改动会被热换（守护进程原地重载、领养在跑单元，不排空、不重跑），但仍是全体共用的代码，先跑本地回归。
  发布以完整代码代原子切换；进程已算完但尚未写收据时直接接回已有结果。

## 组成

| 文件 | 跑在 | 职责 |
| --- | --- | --- |
| `node/pcnode_daemon.py` | PC/WSL | 常驻调度：收件箱、多负载公平接纳与资源申报、轻重两档并发、SIGSTOP 冻结、内存刹车、超时、撤回、孤儿清理、内容寻址闭包库、心跳 |
| `node/pcnode_unit.py` | PC/WSL | 单元执行：`lean`（编一个模块）与 `cmd`（任意命令），每单元一个垫片进程组，结果落盘供热重载/崩溃后领养 |
| `node/setctl.py` | PC/WSL | 改 `control.json`（并发上限、暂停） |
| `node/bench.py` | PC/WSL | 同一组单元逐配置重跑的并发基准 |
| `mac/pcnode.py` | Mac | 核心：SSH/WSL 传输、部署与保活、投递（闭包增量）、增量回收、通用校验、对账、清理、主循环、`Workload` 基类 |
| `mac/lean_closure.py` | Mac | Lean import 闭包（全头部、注释感知）与产物定位 |
| `mac/lean_modules.py` | Mac | 适配器 + CLI：Lean 模块批 |
| `mac/cmd_batch.py` | Mac | 适配器 + CLI：命令批 |
| `mac/run_supervisor.sh` | Mac | 守护脚本（退出码 0 停、75 立即重启、其他 30 s 后重启） |
| `mac/start.sh` | Mac | 以新会话脱离终端启动守护脚本，并把命令记入 `<state>/resume.json` |
| `mac/resume.sh` + `mac/com.homework.computenode.resume.plist` | Mac | 登录时恢复未完成的负载（LaunchAgent） |
| `mac/status.py` | Mac | 只读状态：节点心跳、各负载份额，与各 state 的进度、速率、ETA、失败 |
| `mac/cancel.py` | Mac | 撤回一个负载已投出的单元（停循环 + 节点 `CANCEL`） |
| `mac/node_env.py` | Mac | 把 uv 项目的锁定环境镜像到节点 `~/pcnode/envs/<名>` |

节点代码由 Mac 端每轮比对哈希后热部署；守护进程代码一变即原地 `execv` 重载并领养在跑单元（不排空）。
**改 `node/*.py` 请在副本里改好再替换**，否则编辑中途的版本会被推上节点。

## 写一个新适配器

子类化 `mac/pcnode.py` 的 `Workload`，实现：

| 方法 | 含义 |
| --- | --- |
| `candidates(shipped)` | 现在可以跑的单元（排除已收、已失败与 `shipped` 中的 id） |
| `payload(units)` | 随单元上传到 `src/` 的文件 `(本地路径, src 下相对路径)` |
| `closure(units)` | 单元需要的共享文件 `(本地路径, 视图内相对路径)`：节点按内容去重，只传没有的；Lean 用 `lean_closure` |
| `accept(record, files)` | 已通过通用校验的 exit-0 收据；把要的文件移走，写自己的账本，返回 `promoted`/`paid`/`failed` |
| `failed(record, reasons)` | 单元在节点失败或校验不过（通用失败日志已写） |
| `tick()` / `finished()` | 每轮投递之后的下游工作（如装配）与完成判定；`tick` 返回 `total`/`accepted`/`failed` 供进度与 ETA，长活放线程池，别拖住循环 |

单元是带唯一 `id` 与 `kind` 的 dict（字段见 ARCHITECTURE.md）。**同一 id 永不重投**：要重跑就换 id，
惯例是 `名字@源哈希前缀`，改源即自动重投（`lean_modules` 即如此）。然后 `run(workload, Config.load(...), state)`。
J 这类"生成源 → 编块 → 收据进领域账本 → 整行装配"的流程正好对应 `candidates/accept/tick`。

## 运维

- 一眼看全：`mac/status.py`；细节：`<state>/status.json`、`progress.jsonl`、`loop.log`、`failures.jsonl`，
  节点 `~/pcnode/daemon.log`、`daemon.heartbeat.json`；
- 调并发：`python3 ~/pcnode/bin/setctl.py --home ~/pcnode day_workers=10`（2 s 内生效，全局）；默认白天/夜间都是 16，重单元合计最多 8；
- 守护进程**按需启停**：有负载时由 Mac 循环经 WMI 拉起，空闲 30 分钟（`idle_exit_minutes`）自行退出，WSL 随之关机并把内存还给
  Windows；手动停：`touch ~/pcnode/STOP`（排空后退出）；
- **登录自动恢复**：LaunchAgent `com.homework.computenode.resume`（plist 在 `mac/`，已装在 `~/Library/LaunchAgents/`）
  登录时运行 `mac/resume.sh`，按各 state 的 `resume.json`（`start.sh` 记录的命令）拉起未完成的负载；有 `FINISHED`（跑完）、
  `STOP` 或循环仍活着的跳过。日志 `~/Library/Logs/computenode-resume.log`。重装：复制 plist 后
  `launchctl bootstrap gui/$(id -u) ~/Library/LaunchAgents/com.homework.computenode.resume.plist`。
  前提：macOS 已允许 Homebrew Python 访问"文稿"（系统设置 → 隐私与安全性 → 文件和文件夹）；后台拉起的 Python 未授权时会
  卡在权限弹窗上，Homebrew 升级 Python 后可能要再允许一次。

## 不变量与踩过的坑

- **内存采样只读 `/proc/<pid>/status`**。`smaps_rollup` 要走完约 17 GB olean 映射的页表，每次约 150 ms CPU 且持目标进程 mmap 锁；
  J 节点因此常年白烧约 3 个核（修复后同组块吞吐 +13%）。
- **Lean 用 `-M32000`**：`-M` 把映射的 olean 页算进内存，`-M16000` 会把超限误报成 `decide … stuck`。
- **闭包根不能放 `/tmp`，闭包不全必须拦住投递**：J 实例曾因 `/private/tmp` 下的根在 Mac 重启后消失，静默投出约 2000 个缺依赖的块；
  `lean_modules` 在候选阶段就拦下缺产物的模块。
- **闭包要带 `.ir.sig`**（缺了 Aesop 类初始化报 "(interpreter) unknown declaration"）；**import 头必须完整扫描**（有模块导入整个 Mathlib）。
- **守护进程必须由 WMI 创建的 `wsl.exe` 托管**：WSL 在最后一个 wsl.exe 客户端退出时关闭发行版，SSH 里 setsid/nohup 起的进程也会死。
- **换代码不排空**：旧做法是 STOP 排空再重启，期间全节点不接新单元；2026-10-07 一个 48 小时上限的 c14 单元在跑，排空等于让所有线程停摆。
  现在守护进程原地 `execv`（PID 不变、WMI 宿主不断），单元由垫片执行、结果落盘，新映像领养后照常收据。
- **并发看物理核与内存两件事**：9800X3D 上 8 个已占满物理核，但超线程仍有效（8→16 吞吐 +48%）；轻块约 4 GB，重块 10–20 GB，
  重块簇只能靠内存决定并发，所以重单元共用一个 8 slots 的池、多出的冻结，而不是固定 worker 数；"重"按单元与所属负载判定，
  一个负载的重批次不压别的负载的轻单元。`MemAvailable` 含 olean 页缓存，不能单独当安全余量。
- **提交标记写在最后**：投递以节点 `READY` 之后写的 `job.json` 为准；收据以写完的 receipt 为准；中途任何崩溃都能在下次启动对账恢复。
- **闭包库内容寻址**：旧的按路径共享库让后投的负载覆盖先投的版本，跑着的单元可能静默链接到错的依赖；
  现在 blob 只读、按 sha256 命名、永不覆盖，每个 job 一个硬链接视图（细节见 ARCHITECTURE.md）。
- **一轮只开一次 SSH 回收、一次清理**：J 实例按任务逐个开 SSH，链路抖动时成批失败；节点保留约 1 小时存量
  （`low_water` 1000），断网也不至于几分钟就空转；投递先于下游工作，下游慢不拖住投递。
- **执行器异常立即写 exit −2 收据**（源变、缺目录、缺解释器），不重试：J 测试中曾因缺 `src/` 每 15 秒无限重试。
- **Mac 侧子进程要带 `lake env`**：J 实例曾在无 `lake env` 下生成源，新模块缺 Mathlib 卡住最后一行。
- **Tailscale 身份唯一**：迁移助理会把机器密钥一并复制，两台 Mac 抢同一身份导致断网与绕中继；另一台须彻底重置 Tailscale 状态
  （退出登录无效）。直连时 Mac→PC 延迟个位数毫秒、投递 300 块约 40 秒。

## 信任边界

Mac 只核对 host、Lean githash 与文件哈希，不在 Mac 上重跑内核：节点是**可信构建机**。J 接受这一点；
若别的计算要以节点产物支撑证明结论，在终产物上加一道 Mac 端复核（如 lean4checker 或本地重编抽检）。
把节点产物喂给 `lake build`（而非走 `LEAN_PATH` 缓存）需要 lake trace 认可，**尚未验证** `[⚠️]`。

## 与 J 实例的关系

`Lean/scratch/PcNode` 是 J 的专用流水线（已完成、已停机；保留作历史实例，闭包库已迁到 `~/pcnode/lib`，`~/jnode/lib` 为软链接）。
新负载一律走本目录；**一台节点只常驻一个守护进程**（`~/pcnode`）。

## 验证记录

本地基础设施回归：`python3 -m unittest discover -s ComputeNode/tests -v`，无远程写入。
覆盖确认丢失与断网后对账、同名负载投递隔离、环境同步失败与缓存失效、进程登记与 PID 复用、
零并发/显式暂停、48 MiB 日志输出的有界内存、基准重复单元的输出隔离；多负载公平接纳（字母序靠前的大批次不再饿死小负载）、
优先级分层、GPU 独占与让行、内存预留、撤回（排队与在跑）、按负载补货、内容寻址闭包（同路径不同版本隔离、只传未知 blob、
对账补记索引、旧库硬链接收编、损坏 blob 拦截）。

2026-10-07（Python 环境）：`lalanine40k` 环境 49 秒镜像到节点（Python 3.13.13 与 Mac 相同）；经 cmd 单元在节点算出的
python-flint 300 位 √2·π 与 pyscf H₂/cc-pVDZ RHF 能量（−1.128700093556）和 Mac arm64 逐位一致。

2026-10-07（真实 `~/pcnode`，两个负载同时跑）：共享索引使导入 Mathlib 的模块零闭包上传；一次 SSH 同时收回两个任务的收据；
无 payload 的命令单元正常执行；执行器异常收到单次 exit −2 失败；代码热部署后守护进程 20 秒内重启；空闲退出后 WSL 关机、`vmmem` 消失。

2026-10-05（独立测试目录、≤3 worker，与 J 并行）：

Lean 批：依赖按轮放行（B 等 A 收回后才投、A 的产物作为闭包随行）、坏模块失败且其依赖者判死、改源只重投该模块、
PC 产物在 Mac 上可直接 import。命令批：正常/失败退出/缺输出（97）/超时（124，只计清醒时间）/多 slot、
冻结与解冻、守护进程被杀后 Mac 端拉起并清理孤儿进程组后重跑、启动对账撤回半投递任务、跑完守护脚本自退。
