"""Fresh focused Lean checks and task-owned LSP diagnostics; no project artifact writes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import subprocess
import tempfile
import threading
import time

from verify import HERE, freeze_check


def lsp_check(project, env, paths):
    process = subprocess.Popen(["lean", "--server"], cwd=project, env=env,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    inbox = queue.Queue()

    def reader():
        while True:
            header = process.stdout.readline()
            if not header:
                return
            if not header.startswith(b"Content-Length:"):
                continue
            length = int(header.split(b":")[1])
            while process.stdout.readline() not in (b"\r\n", b"\n", b""):
                pass
            inbox.put(json.loads(process.stdout.read(length)))

    threading.Thread(target=reader, daemon=True).start()

    def send(message):
        body = json.dumps(dict(jsonrpc="2.0", **message)).encode()
        process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode()+body)
        process.stdin.flush()

    def until(predicate, seconds=45):
        deadline = time.monotonic()+seconds
        messages = []
        while time.monotonic() < deadline:
            try:
                item = inbox.get(timeout=min(1, max(0.001, deadline-time.monotonic())))
            except queue.Empty:
                if process.poll() is not None:
                    raise RuntimeError("task-owned LSP exited")
                continue
            messages.append(item)
            if predicate(item):
                return messages
        raise TimeoutError("task-owned LSP response timeout")

    try:
        send({"id": 1, "method": "initialize", "params": {"processId": os.getpid(),
              "rootUri": project.as_uri(), "capabilities": {}}})
        until(lambda item: item.get("id") == 1)
        send({"method": "initialized", "params": {}})
        results = []
        for index, path in enumerate(paths, 2):
            uri = path.as_uri()
            send({"method": "textDocument/didOpen", "params": {"textDocument": {
                "uri": uri, "languageId": "lean4", "version": 1, "text": path.read_text()}}})
            send({"id": index, "method": "textDocument/documentSymbol",
                  "params": {"textDocument": {"uri": uri}}})
            completed = {"response": None, "idle": False, "diagnostics": None}

            def ready(item):
                if item.get("id") == index:
                    completed["response"] = item
                params = item.get("params", {})
                if item.get("method") == "$/lean/fileProgress" and params.get("textDocument", {}).get("uri") == uri:
                    completed["idle"] = not params.get("processing", [])
                if item.get("method") == "textDocument/publishDiagnostics" and params.get("uri") == uri:
                    completed["diagnostics"] = params["diagnostics"]
                return completed["response"] is not None and completed["idle"] and completed["diagnostics"] is not None

            until(ready)
            response = completed["response"]
            if "error" in response:
                raise RuntimeError(response["error"])
            diagnostics = completed["diagnostics"]
            bad = [d for d in diagnostics if d.get("severity", 1) <= 2]
            if bad:
                raise RuntimeError(json.dumps(bad))
            results.append({"file": path.name, "errors": 0, "warnings": 0,
                            "symbol_count": len(response.get("result") or []),
                            "method": "task-owned lean --server; documentSymbol, idle fileProgress, published diagnostics"})
            send({"method": "textDocument/didClose", "params": {"textDocument": {"uri": uri}}})
        return results
    finally:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake-project", required=True, type=Path,
                        help="Existing offline pinned Lean cache; read only")
    args = parser.parse_args()
    project = args.lake_project.resolve()
    freeze = freeze_check()
    root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=HERE, text=True).strip())
    for filename in ("lean-toolchain", "lake-manifest.json"):
        if (project/filename).read_bytes() != (root/"Lean"/filename).read_bytes():
            raise ValueError("shared cache pins differ from worktree")
    env = json.loads(subprocess.check_output(["lake", "env", "python3", "-c",
                     "import json,os; print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-lean-") as temporary:
        env["LEAN_PATH"] = temporary+os.pathsep+env.get("LEAN_PATH", "")
        for name in ("Collection", "Consumer"):
            command = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+str(HERE),
                       "-o", str(Path(temporary)/(name+".olean")), str(HERE/(name+".lean"))]
            result = subprocess.run(command, cwd=project, env=env, text=True,
                                    capture_output=True, timeout=120)
            checks.append({"file": name+".lean", "exit_code": result.returncode,
                           "stdout": result.stdout, "stderr": result.stderr,
                           "flags": ["--trust=0", "-DwarningAsError=true"]})
            print(f"{name}.lean strict exit={result.returncode}")
            print(result.stdout+result.stderr, end="")
            if result.returncode:
                raise RuntimeError("focused Lean check failed")
        lsp = lsp_check(project, env, [HERE/"Collection.lean", HERE/"Consumer.lean"])
    receipt = {"schema": "p23-collected-source-lean-certification/v1", "status": "certified",
               "classification": "bounded subordinate finite real optical producer and independent consumer",
               "freeze": freeze, "strict_checks": checks, "lsp": lsp,
               "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "scope": "Finite real source amplitudes, polarization-preserving local loss columns; no original root installation, complex channel certification or empirical identity.",
               "sha256": {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                          for name in ("Collection.lean", "Consumer.lean", "certify.py", "criterion.md")},
               "toolchain": (project/"lean-toolchain").read_text().strip()}
    (HERE/"certification.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print("PASS: focused trust0/werror, all candidate axioms, source dependency closure, independent consumer, LSP")


if __name__ == "__main__":
    main()
