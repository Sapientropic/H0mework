# Supplementary material: complete proofs

**We Found No Magic in This Mighty Universe: Common-Source Generation and Classical–Quantum Correspondence in a Spin×SU(7) Theory**

**Author: Jian Gao (高健)**

This supplement gives complete written proofs and check accounts of Theorems 6.7–6.14, Propositions 9.1–9.3 and the results at the end of §6.9 and in §9.2 of the main text. The main text states the results and gives proof ideas; here each result is given its objects and domain, actual inputs and quantifiers, construction, key lemmas, decisive derivation, and the direct use of the same object in later results, and is finally matched to its formal declaration or frozen receipt. Notation is that of the main text, and numbers of definitions, theorems and equations refer to the main text. The proofs of §2–§5, §6.1–§6.6, §7 and §8 are complete in the main text and Appendices A–C and are not repeated.

The “formal correspondence” at the end of each section lists the Lean declarations or frozen receipts that carry the result; the source commits, full paths and receipt identities are in Appendices D.7–D.8 of the main text, and the public reproduction entry is in its “Code and data availability”. The pinned-commit aliases AB, AC, AD, AE, CAP, H, F are defined in Appendix D.1 and D.7–D.8; this supplement only checked the pinned source files and rebuilt, compiled or ran nothing.

Evidence identities come in five classes, marked item by item: **formal theorem** (a declaration verified by the Lean kernel), **finite exact computation** (a finite identity decided term by term in the proof kernel, with the deciding means reported faithfully), **fixed exact source program with independent recomputation** (an exact computation program at a pinned commit, each accompanied by an independent-implementation recomputation at the same commit), **dual-implementation numerical check** (frozen receipts produced separately by two independent implementations, with tolerances), and **statistical contract** (an anytime test with a pre-registered error rate). Physical interpretation and hardware identity are not enlarged under any class.

---

## S0 Common notation and tools

The following objects recur throughout; we define them once.

**S0.1 Configuration and test spaces.** Fixed source and original action (3.1). $\mathscr U_{103}=\mathscr U_q\times\mathscr U_x\times\mathbb R^{36}$ is the common noncharacteristic domain (the source-containing connected component of $v_e>0$, $\det h\ne0$, $g_{00}\ne0$, $h^{00}\ne0$, $\det D_9\ne0$ and the fourth-order time–electric block $\det\mathscr M\ne0$), and $\mathscr U_{100}$ is the three-stabilizer section (S1). $\mathcal I=\{+,-\}\times\{0,1,2,3\}\times(\Lambda^6\sqcup\Lambda^2\sqcup\Lambda^4)$ is the index set of 504 CAR modes, $\mathcal F_{504}=\Lambda^*\mathbb C^{504}$. The configuration Hilbert space $\mathscr H$ is given by the weighted $L^2$ direct sum of (S1.5); the quantum test space $\mathcal Q=C_c^\infty(\mathscr U_{100};\mathcal F_{504})$ is dense in it.

**S0.2 Cutoff compression and retained term.** For a cutoff index $F$ (a finite index of the Gauss unitary history), $C_F(p)$ denotes the self-adjoint compression at momentum $p$ of the complete native Hamiltonian $H_0$ to $F$; $A_F$ is the retained term of the uncut Yukawa; $K_F(p)=C_F(p)+A_F$ is the actual generator. $C_F$ preserves the $\Lambda^6$ occupation grading and $A_F$ raises it by one (S1.3). $T_p(t)=e^{-itK_F(p)}$, $R_p(z)=(K_F(p)-z)^{-1}$ ($z$ non-real). Cutoff indices are directed by inclusion; “for cofinal $F$” means on all $F$ beyond some terminal segment of the source filter.

**S0.3 Response point and five-factor kernel.** A **response point** $q$ carries: a cutoff index $F$, left/right matter momenta $p_L,p_R$, two non-real spectral parameters $z,w$ ($\operatorname{Im}z\ne0$, $\operatorname{Im}w\ne0$), a preparation precision $\varepsilon>0$, a finite window $T$ and a source field curve. The current read-port $J$ is the quantization of the mother action's first variation. The five-factor kernel is
$$\mathcal K_q(t)=T_{p_R}(-t)\,R_{p_R}(z)\,J\,R_{p_L}(w)\,T_{p_L}(t).\tag{S0.1}$$
$\mathbb C^{289}$ is the space of real directions of the nine field groups, and $H_{289}(p)$ is the Jacobi matrix at four complex momenta $p$ (S5).

**S0.4 Resolvent and Duhamel tools.** The resolvent of a self-adjoint operator $A$ satisfies $\|(A-z)^{-1}\|\le|\operatorname{Im}z|^{-1}$ ($z$ non-real), and the resolvent-difference formula $R_p-R_k=R_p(C_F(k)-C_F(p))R_k$. The unitary Duhamel formula $e^{-itB}-e^{-itA}=-i\int_0^te^{-i(t-s)B}(B-A)e^{-isA}ds$ is used in the operator-norm topology. The Bochner integral $\int_0^\infty e^{-\lambda t}\Phi_t\,dt$ converges for a uniformly bounded strongly continuous operator semigroup when $\operatorname{Re}\lambda>0$; for the two-leg action $\Phi_t(X)=T_{p+k}(-t)XT_p(t)$ it is defined componentwise.

**S0.5 How the finite exact identities are checked.** Many proofs here reduce to finitely many identities decided term by term in the proof kernel: e.g. the 3071-term dictionary of $H_{289}$ (coefficients in $\mathbb Q(\sqrt2,\sqrt{15})$), the 576-entry polynomial matrix product, and the explicit inverse of a 289-dimensional matrix. The deciding means are stated faithfully at each section's “decisive derivation”; three kinds are actually used: termwise equality of canonicalized term lists and dictionaries by `decide +kernel` (the kernel reduces both sides to the same canonical form); scalar equalities in the coefficient field $\mathbb Q(\sqrt2,\sqrt{15})$ by `ring`, `norm_num`, `field_simp`, `linear_combination`, `nlinarith` term by term; finite-dimensional matrix equalities, after indexwise expansion, by `decide +kernel` and `fin_cases` together with the scalar decisions. Such decisions are theorems, not numerical fits.

**S0.6 How the data-type declarations are checked.** The items of Propositions 9.1–9.3 marked “dual-implementation check” or “statistical contract” have their numerical conclusions produced separately by two programs that share no forward computation (the primary and the independent implementation), each producing a frozen first receipt which is then cross-checked; criterion files are frozen before execution, and statistical contracts pre-register a total error budget (e.g. the joint $\alpha=1/20$). Receipt identities are listed item by item in S9 and Appendix D.8.

---

## S1 Theorem 6.7: the common quantum Hamiltonian

**Objects and domain.** The fixed source and the original action (3.1) satisfying the noncharacteristic conditions of §4: $v_e>0$, $\det h\ne0$, $g_{00}\ne0$, $h^{00}\ne0$, $\det D_9\ne0$, $\det\mathscr M\ne0$ (see S0.1 and (3.2)–(3.6), (4.1)–(4.6) of the main text). The matter configuration is the complete 252-dimensional Dirac×colour symbol $\psi$ together with the independent dual $\chi$.

**Inputs and quantifiers.** All conclusions hold for every source neighbourhood satisfying the noncharacteristic conditions; “61”, “504”, “103”, “100”, “392” are fixed source-generated dimensions, not tunable parameters. The identity of item (3) holds for every four complex momenta $p$.

**Construction.** Four steps: the canonical one-form and CCR/CAR; the four energies on a common domain; the three-stabilizer section and measure; the action recognition.

**(1) The canonical carrier.**

*Legendre map.* The spatial Gram $h=e_{\rm sp}^{\mathsf T}\eta e_{\rm sp}$ gives the coframe six-velocity map
$$\Pi_e=M_e\dot e+b_e,\qquad Z^{\mathsf T}(\Pi_e-b_e)=0,\qquad \dot e=Q_e(\Pi_e-b_e)+Z\lambda,\tag{S1.1}$$
where $M_e=D_h^{\mathsf T}B_hD_h$ ($B_h=(4v_e)^{-1}\operatorname{Hess}_h\det h$), of rank six when $\det h\ne0$, and $Q_e=R_hB_h^{-1}R_h^{\mathsf T}$ is generated by an explicit right inverse rather than an arbitrary pseudoinverse; the ten primary constraints are given by the ten columns of $Z$ (four time columns and six Lorentz columns). The scalar map requires $h^{00}\ne0$: $\Pi_\phi=h^{00}(\dot\phi+\rho^{70}_{A_0}\phi)+b_\phi$. The gauge map requires $g_{00}\ne0$: $K_E^{-1}=-\tfrac{\sigma v_e}{g_{00}}(g^{-1})_{\rm sp}$, with twelve time components of momentum zero. The matter dual is $p=-i\chi E$ with $E=v_e(e^{-1})^0{}_a i\gamma^a\otimes I_{63}$; $\chi$ is not pre-identified with $\psi^\dagger$. The common canonical one-form is
$$\Theta=\Pi_e\cdot\delta e+\Pi_\phi\cdot\delta\phi+\sum_i\Pi_A^i\cdot\delta A_i+\operatorname{Re}(ip\,\delta\psi),\tag{S1.2}$$
with energy $H_{\rm cl}=H_e+H_\phi+H_{\rm g}+H_{\psi,{\rm rem}}$ and common twelve-dimensional Gauss $\mathcal G=\mathcal G_A+\Pi_\phi^{\mathsf T}\rho^{70}\phi+\operatorname{Re}(ip\,\rho^{252}\psi)$.

*61 CCR pairs.* Take a fixed real basis $R\in\mathbb R^{70\times61}$ of $\ker O^{\mathsf T}$ ($O=(O_1,\dots,O_{12})$ the original gauge–scalar orbit matrix, $\operatorname{rank}O=9$, $D_9=O_b^{\mathsf T}O_b$ equal to $256$ at the source). On the scalar constraint map write $\phi=v+Rx$, $\Pi_\phi=R^\vee\pi+O_b\zeta$ ($R^\vee=R(R^{\mathsf T}R)^{-1}$, $\zeta$ generated by the remainders of the nine unstable Gauss conditions through $D_9^{-\mathsf T}$). Since $O_b^{\mathsf T}R=0$, $\Theta$ pulls back exactly to $\pi\cdot\delta x$ on this map, giving 61 CCR pairs $[x_j,-i\partial_{x_k}]=i\delta_{jk}$.

*504-mode two-branch CAR.* The real canonical coordinates of the matter one-form $\operatorname{Re}(ip\,\delta\psi)$ are $(\operatorname{Re}\psi,\operatorname{Im}\psi)$ with momenta $(-\operatorname{Im}p,-\operatorname{Re}p)$. After complexifying the two independent real branches, the mode indices are $\mathcal I$ (S0.1), $|\mathcal I|=504$, and the creation/annihilation operators satisfy the standard CAR (equation (5.2) of the main text). The two-branch gauge-current matrix is $Q_a=\operatorname{diag}(i\rho_a^{252},i\overline{\rho_a^{252}})$; the two-branch realization of the matter Hamiltonian matrix $M$ is $\operatorname{diag}(M,-\overline M)$. This is one CAR quantization of the 504-dimensional whole, not a separate quantization of $\psi$ and $\chi$ paired afterwards.

*Common domain of the four energies.* Writing the coframe six velocities as combinations of orthogonal momenta $\kappa_r=-i\partial_{q_r}$ and Lorentz currents (lower-triangular spatial parametrization $L(q)$, $v=\det L$), the four energies actually add on
$$\mathscr D_{103}=C_c^\infty(\mathscr U_{103};\mathbb C)\otimes\mathcal F_{504}\tag{S1.3}$$
and every finite ordered composite preserves this domain. Each coefficient is generated by inverses of the given nondegenerate matrices and finitely many differentiations, hence smooth on $\mathscr U_{103}$; the cross principal part has 944 nonzero entries on the original coefficients, and the 61 original Yukawa force directions are retained. Note $103=6+61+36$ (coframe, scalar tangential, gauge connection): a configuration dimension, not a propagating-quotient dimension.

**(2) Section, measure and the common Hamiltonian.**

*Three stabilizers.* Let $S\in\mathbb R^{12\times3}$ span $\ker O$. With the original Gram $G$ define $B=E_b-S(S^{\mathsf T}GS)^{-1}S^{\mathsf T}GE_b$; then $[B,S]$ is a complete basis of the gauge algebra and the three stabilizers satisfy $[S_a,S_b]=-2\epsilon_{abc}S_c$; the original action further gives $[S_a,B]=BC_a$, $\rho_{S_a}O_b=O_bC_a$, $\rho_{S_a}R=RT_a$ and $C_a^{\mathsf T}D_9+D_9C_a=0$.

> **Lemma S1.1 (The three stabilizers commute with the common action).** The $\widehat G_a$ generated by the three stabilizers on $\mathscr D_{103}$ satisfy $[\widehat G_a,\widehat H]=0$, and their common kernel is nonzero and invariant under every finite ordered composite of the four energies.

*Proof.* By the covariance laws above, $V_aD_9=-C_a^{\mathsf T}D_9-D_9C_a$, hence $V_aF=C_aF+FC_a^{\mathsf T}$ ($F=D_9^{-\mathsf T}$); substituting into the ordered expansion of the momentum square, the variations of the normal coefficients and the current matrices cancel slot by slot, without commuting inner momenta. The gauge part uses the original Gram invariance and the Lie-derivative laws; the coframe part commutes spin matrices and the exterior-power gauge action. Nonzeroness is given by occupation vectors preserving the three stabilizers (e.g. $|(7,259)\rangle$) times compactly supported functions; a charged single mode gives a nonzero action, so the common kernel is a proper subspace of the Fock fibre. ∎

*Quantum section.* The quantum configuration is the 103-dimensional boson part (the matter is already realized by the CAR fibre). The same three gauge pivots as the classical reduction are used: at the designated source the orbit matrix $M=I_p^{\mathsf T}V$ satisfies $\det M_*=-54\sqrt2/125\ne0$. The local orbit map $\Phi(\alpha,z)=\exp(\sum_a\alpha_aL_a)(z_{\rm base}+I_fz)$ has an invertible derivative at the source point, and the inverse function theorem gives a nonempty local chart. The extension $\mathcal E$ and restriction $\mathcal R$ satisfy $\mathcal R\mathcal E=I$, $\widehat G_a\mathcal Ef=0$; the reduced operator $H_{100}=\mathcal R\widehat H\mathcal E$ preserves every finite composite (by $\widehat H\mathcal E=\mathcal EH_{100}$ of Lemma S1.1).

*Measure cancellation and half-density.* The orbit Jacobian gives the section weight $\rho_3(z)=8a_1^2a_{12}>0$ (value $54\sqrt2/125$ at the source). The nine unstable scalar conditions are second-class constraints: the product of the three factors — fixed-basis volume, normal-momentum integral and second-class determinant — is
$$\frac1{256}\cdot\frac{256}{|\det D_9|}\cdot|\det D_9|=1,\tag{S1.4}$$
so the actual measure of the quantum section is $\rho_3$, not multiplied by $|\det D_9|$ again; the density of the twelve-dimensional geometric extension is separately $\rho_{12}=|\det D_9|\rho_3/256$, a different responsibility. The sector of occupation number $m$ carries weight $v^{m+2}$:
$$\langle f,g\rangle=\sum_{w\subset\mathcal I}\int_{\mathscr U_{100}}\overline{f_w}g_w\,\rho_3v^{m+2}dz,\qquad \mathscr H=\bigoplus_{w}L^2(\rho_3v^{m+2}dz).\tag{S1.5}$$
The compactly supported smooth domain is dense in it (the cutoff–approximate–mollify argument per occupation number). The half-density map $(Uf)_w=\rho_3^{1/2}v^{1+m/2}f_w$ is a surjective isometry to the flat measure; the $v^{m+2}$ factor is required for the coframe adjoint closure.

*The formal adjoint pair and minimal closure.* On the same dense domain $\mathscr D_{100}$ of (S1.3)–(S1.5), let $H_0$ be the sum of the coframe, the formally ordered scalar ($\sum_j\Pi_j^\dagger\Pi_j/(2h^{00})$ ordering), the gauge and the non-Yukawa matter energies, and $Y$ the CAR realization of the original one-directional Yukawa.

> **Lemma S1.2 (Adjoint pair and closed graphs).** $H_0$ is formally symmetric; the complete $H=H_0+Y$ and the independent $H^\sharp=H_0+Y^\dagger$ satisfy $\langle f,Hg\rangle=\langle H^\sharp f,g\rangle$ ($f,g\in\mathscr D_{100}$). Both are closable, each with a single-valued minimal graph closure. The common one-body nullspace of the original full Yukawa and its adjoint has 392 modes across the two independent branches; its Fock carrier reduces $H_0$, on which $Y=Y^\dagger=0$ and the restriction is formally symmetric.

*Proof.* Termwise integration by parts: the scalar uses the designated $\Pi^\dagger\Pi$ ordering; the gauge Gram and magnetic derivatives are symmetric; the coframe's momentum, mixed-current, normal-product and coefficient-derivative terms pair under the weight $v^{m+2}$; the non-Yukawa matter matrix is Hermitian under the two-branch pairing. Only the original one-directional $Y$ becomes $Y^\dagger$ under adjunction—the unique source of asymmetry, and a substantive counterexample: on the two-particle vector $|144,396\rangle$, the source point gives $\|Y|144,396\rangle\|^2=4N^2=216/125$ and $Y^2\ne0$, so $Y$ on the whole Fock action is neither zero nor implicitly symmetric. The nonzero spectrum of the 70 Yukawa Grams is $10N^2$ (multiplicity 42) and $30N^2$ (multiplicity 14), with common two-sided nullspace of 196 dimensions per branch; projecting to the common kernel gives the $196\times2=392$ mode restriction.

Closeness: if $f_n\to0$ and $Hf_n\to g$, then for every $h\in\mathscr D_{100}$, $\langle h,g\rangle=\lim_n\langle H^\sharp h,f_n\rangle=0$, and density gives $g=0$; swapping $H,H^\sharp$ is symmetric. This gives the minimal graph closure of each, without choosing a self-adjoint extension first. ∎

*Four-time Weyl representation and all canonical motions.* On $U\mathscr D_{100}$ there is a quadratic momentum symbol $\sigma_0+Y$, uniquely read from the original coefficients, with $\operatorname{Op}_W(\sigma_0+Y)=UHU^{-1}$: first read the second-order $K$, then use the first divergence correction to read the first-order $B$, and restore the zeroth-order term; the coframe's $\operatorname{divdiv}(K)/4$ merges with the half-density potential into $n(3\mathrm{Number}^2+18\mathrm{Number}+20)/(16v)$; the Hermiticity of $\sigma_0$ is given by termwise integration by parts and Lemma S1.2; $Y$ contains no momentum and $U$ is scalar per occupation number, so it is preserved as is. Hence $H$ generates all canonical motions of the 100 CCR pairs and the 504 CAR pairs.

**(3) Action recognition.** The original action–force coefficient is the configuration-dependent $4W$, with $W\ge1$ generated by the original scalar Gram. The actual core $K(p)$ contains the original full Yukawa, the configuration matter, the retained time and spin terms and the physical momentum, and satisfies for every $p$ exactly
$$S_{\rm phys}(p)+Y=S_{\rm nat}+S_{\rm cf}+K(p)-K_{\rm ret}.\tag{S1.6}$$
The recognition is slotwise: every second-order density term of $S_{\rm phys}$ is recovered by the native sector $S_{\rm nat}$, the coframe part $S_{\rm cf}$ and $K(p)$, and the remaining slots are exactly $K_{\rm ret}$; $K_{\rm ret}$ is not an externally supplied remainder—it is given by the original action itself as part of the same core's definition. The identity holds term by term on the $\mathbb C^{289}$ symbol dictionary, with the configuration dependence of $W$ kept in every direction.

**Direct use.** The carrier and minimal closure of (1)(2) are the carriers of $H_0$, $Y$, $R$ and the prepared state of Theorem 6.8; the $K(p)$ and $4W$ of (3) enter the genuinely varying response of Theorem 6.9 and the Ward channels of Theorem 6.10; $\mathscr H$ and its graded structure are the underlying carrier of the spectral argument of Theorem 6.12 and the readout model of Proposition 9.2.

**Formal correspondence.** The sub-conclusions of Theorem 6.7(1)(2) are pinned item by item to earlier commits of the constrained-local-quantization source programs; the production mouths and evidence classes are as follows (`ecd/` abbreviates `Verification/physics/low-energy-phenomenology/external-composite-decay/`; aliases and commits are in Appendix D.7 of the main text):

| Sub-conclusion | Pinned commit | Production mouth | Evidence class |
| --- | --- | --- | --- |
| 61 CCR pairs ($O_b^{\mathsf T}R=0$, $\Theta$ pulls back exactly) | `85cb5386…` | `ecd/source_scalar_gauss_reduction.py` and `independent_*.py` | fixed exact source program and its independent recomputation |
| 103-dimensional common domain, 944 nonzero cross entries, 61 Yukawa directions | `85cb5386…` | `ecd/source_joint_local_quantum.py` and `independent_*.py` | fixed exact source program and its independent recomputation |
| 504-mode two-branch CAR and gauge-current matrix $Q_a$ | `85cb5386…` | the same two programs | fixed exact source program and its independent recomputation |
| three-stabilizer covariance laws and nonzero common kernel (Lemma S1.1) | `f9b73392…` | `ecd/source_quantum_stabilizer.py` and `independent_source_quantum_stabilizer.py` | fixed exact source program and its independent recomputation |
| classical reduced phase-space map and gauge pivots | `f9b73392…` | `ecd/source_stabilizer_phase_reduction.py` and `independent_source_stabilizer_phase_reduction.py` | fixed exact source program and its independent recomputation |
| quantum section, second-class measure cancellation (S1.4), half-density (S1.5) | `6726f385…` | `ecd/source_quantum_gauss_section.py`, `source_gauss_section_measure.py`, `source_full_gauss_section.py` and same-named `independent_*.py`; `ecd/SecondClassReduction.lean` | fixed exact source program and its independent recomputation + Lean formal theorem (cancellation identity) |
| Hilbert carrier $\mathscr H$, formal symmetry of $H_0$, adjoint pair $(H,H^\sharp)$, minimal closure, 392-mode common-kernel reduction (Lemma S1.2) | `6726f385…` | `ecd/SourceQuantumConfigurationHilbert.lean`, `SourceQuantumHalfDensityHilbert.lean`, `GaussRadialDomain.lean`, `FockFilteredWords.lean`, `GaussSymmetricGraphClosure.lean`, `AntiunitaryDefectPair.lean`, `GaussYukawaCoefficient.lean`, `GaussYukawaNullspace.lean`, `RadialHilbertTransfer.lean`, `GaussHalfDensity.lean`; `ecd/source_hilbert_space.py`, `source_yukawa_cocycle.py`, `source_adjacent_cocycle.py`, `source_symmetric_graph.py`, `source_temporal_cofinal.py` and `independent_*.py` | Lean formal theorems + fixed exact source programs and their independent recomputations (the programs carry the finite-dimensional carrier computations) |
| four-time Weyl representation $\operatorname{Op}_W(\sigma_0+Y)=UHU^{-1}$ | `6726f385…` | `ecd/source_{coframe,scalar,common}_weyl_symbol.py`, `source_common_temporal_form.py` and same-named `independent_*.py` | fixed exact source program and its independent recomputation |
| all canonical motions of the 100 CCR pairs and 504 CAR pairs (configuration port and normal-product port) | `eec031c4…` | `ecd/source_joint_ccr_car_ports.py` and `independent_source_joint_ccr_car_ports.py`; `ecd/JointCCRCarPorts.lean` | fixed exact source program and its independent recomputation + Lean formal theorem (normal-product port) |

The other results of the same source programs at these commits (time-constraint reduction, the quantum time map, the complete 122 inputs and the time/Lorentz constraint orbits, among others) carry no load in this paper; it directly consumes only the sub-conclusions listed in the table above, and the commit aliases are in Appendix D.7 and in the phys.P26 row of S10. The program parts are **not** Lean theorems: they are fixed exact source programs (symbolic/exact arithmetic, not floating-point fits), each accompanied by an independent recomputation program at the same commit as a dual-implementation check; the Lean parts are formal theorems item by item.

Theorem 6.7(3) action recognition: `physical_action_decomposition` of `alpha-source/CanonicalPreparationActionCoreDecomposition.lean`, and `FieldQuantization{Symbols,Core,Contacts}.lean` with the same prefix (Lean formal theorems). Commit AB (the carrier part of 6.7(1)(2) is at the four earlier pinned commits listed in the table).

---

## S2 Theorem 6.8: the all-order clock, the complete fixed $R$ and one source preparation

**Objects and domain.** The carrier $\mathscr H$ of Theorem 6.7, the dense domain $\mathscr D_{100}$, $H=H_0+Y$ and the minimal closed graph. The four time directions of the constraint system are described by the principal-force Jacobi $J_4$ generated by the source coefficient matrices $T,S,C$; $J_4$ is invertible on the source support's positive cone (a condition of the kind of (4.3) of the main text).

**Inputs and quantifiers.** (1) for every order $k\ge0$ and the four time directions $a$; (2) for all scalar test functions; (3) for every $\varepsilon>0$; (4) for the sequence $\varepsilon_n=1/(n+1)$. The clock, $R$, the source operator and the source energy are all generated inside the source, not supplied by the caller.

**Construction and key lemmas.**

**(1) The all-order clock.** The clock recursion is organized by order: the order-$k$ clock is a family of symbols on the four time directions with $k+1$ slots. The initial order puts the source clock value in the zeroth slot and zero elsewhere; the recursion step is
$$C_{k+1}(a,\mathrm{last})=-\sum_b (J_4^{-1})_{ab}\,R_{k+1,b}\tag{S2.1}$$
where $R_{k+1,b}$ is that order's residual symbol on the $b$-th time equation, composed of the 42 order/slot functions already paid at lower orders, the ordered product words and the original 13 time leaves.

> **Lemma S2.1 (Generation and preservation).** (i) the new order is generated exactly by (S2.1); (ii) $C_{k+1}$ agrees with $C_k$ on the first $k+1$ slots (paid lower orders are not rewritten); (iii) for every $k$, $a$, the order-$(k+1)$ four successor forces are identically zero on the closed source-support set (position cone, unit momentum directions, $p\ne0$).

*Proof.* (i)(ii) are direct properties of the recursive definition. (iii) Write that order's residuals as $r_b$ and the new clock as $n_b=-(J_4^{-1}r)_b$; the response of the $b$-th force at order $k+1$ to the new order is linear, equal to $r_b+(J_4n)_b$ (the force-response Jacobi in each direction is exactly $J_4$, the condition being the source clock's nonzeroness on the positive cone). Substituting $n=-J_4^{-1}r$ gives $r+J_4(-J_4^{-1}r)=0$; this uses the actual invertibility of $J_4$ on the source support. ∎

The finite-order derivative budgets of all 100 directions (with multiplicities of repeated directions retained) and the original coefficient table are generated by the same engine.

**(2) The complete fixed $R$.** The energy tail $E_{\rm tail}$ first generates a Fourier kernel (keeping the full translation structure $\pi(\xi+\eta)$) and two-sided Schur bounds; the complete energy form splits on Schwartz inputs as
$$\mathcal E_B(g,f)=\mathcal E_{\rm prin}(g,f)+\mathcal E_{\rm tail}(B;g,f),\tag{S2.2}$$
the two parts integrable separately. Through the Riesz representation, $E_{\rm tail}$ gives a self-adjoint tail operator. Define
$$R=E_{\rm tail}-C_{\rm src},\tag{S2.3}$$
with $C_{\rm src}$ the source-native composition term.

> **Lemma S2.2 (Fixity of $R$).** $R$ is a bounded self-adjoint operator, with source-generated norm bound $\|R\|\le\|E_{\rm tail}\|_{\rm est}+\|C_{\rm src}\|_{\rm est}$; for all original scalar test functions $g,f$, the form composed of the original closed factor $A$ (the closed factor of $B_1^2$) and $R$ satisfies
> $$\langle Ag,Af\rangle+\langle g,Rf\rangle=\mathcal E_B(\check g,\check f),\tag{S2.4}$$
> i.e. exactly the original Weyl energy form of the complete $B_1^2+E_{\rm tail}$. $R$, the source operator $\mathcal T$ composed of $A$ and $R$, and the source energy $E$ are all independent of any preparation precision.

*Proof.* The decomposition (S2.4) expands the left side by the definition of $R$ into a principal part plus a tail part, i.e. (S2.2); self-adjointness is inherited from the energy tail's and the composition term's own self-adjointness. The norm bound: the energy tail's Fourier kernel $k(x,y)$ satisfies a two-sided Schur estimate—the row and column integrals have source-generated finite bounds $S_1=\sup_x\int|k(x,y)|\,dy$, $S_2=\sup_y\int|k(x,y)|\,dx$, and the Schur test gives $\|E_{\rm tail}\|\le\sqrt{S_1S_2}$; the composition term $C_{\rm src}$ has an independent source-generated bound, hence $\|R\|\le\|E_{\rm tail}\|+\|C_{\rm src}\|$. ∎

**(3) One source preparation.** The preparation point is not constructed clause by clause but produced at once by one source factory:

> **Lemma S2.3 (The same preparation point).** For every $\varepsilon>0$, the domain of the source operator contains a point $x_\varepsilon$ satisfying simultaneously: unit norm $\|v_\varepsilon\|=1$; near spectrum $\|\mathcal Tx_\varepsilon-Ex_\varepsilon\|<\varepsilon$; the source-production equality (the prepared image equals the source-created object); the original weak-form identity $\langle\mathcal Tx_\varepsilon,y\rangle=\langle A\hat x_\varepsilon,Ay\rangle+\langle x_\varepsilon,Ry\rangle$; native Yukawa charge readout $=-1$; the norms of the eight external legs controlled by a uniform source-generated bound; an independent time–frequency field (for every $p,k$, Lie index, cutoff, $z,w$ with $\operatorname{Im}z,\operatorname{Im}w>0$ and all discrete indices, the two-time reading converges to the frequency reading); the full Yukawa's domain membership, value equality and cutoff bound
> $$\|Y_{\rm closed}v_\varepsilon-\mathrm{cut}_n(v_\varepsilon)\|\le(915/916)^{n+1}\cdot 916\cdot b,\tag{S2.5}$$
> $b$ the source-generated Yukawa coefficient bound; and limit of the cutoff sequence $=$ the Yukawa value.

*Proof sketch.* The actual mechanism of existence is as follows. The augmented closed form generated by $A,R$ (adding a factor $(1+\|R\|)$ on the graph domain) determines a unique operator $\mathcal T$ and gives a positive, injective bounded resolvent $B=(\mathcal T+1+\|R\|)^{-1}$. Take the source energy
$$E=\|B\|^{-1}-(1+\|R\|):\tag{S2.5a}$$
Since $B$ is a positive bounded operator, $\|B\|$ is a spectral point; for a positive bounded injection, the spectral point $\|B\|$ produces unit approximate eigenvectors (the approximate-spectrum criterion), which through $B^{-1}$ reduce to a unit approximate eigenvector $x_\varepsilon$ of $\mathcal T$ at $E$ (the general lemma being the inverse-operator version for a bounded positive injection). The weak-form identity is the pointwise domain-membership identity of the augmented form and needs no separately chosen point. The eight external legs and the time–frequency convergence are carried by additional fields of the same construction; the four full-Yukawa fields are given by the closed Yukawa graph's original-domain estimates, and the geometric ratio $915/916$ is an explicit upper bound of a ratio of source Yukawa coefficients. ∎

**(4) Two residuals tend to zero together.** Take $\varepsilon_n=1/(n+1)$ and $x_n=x_{\varepsilon_n}$. With the same fixed $R$, $\mathcal T$, $E$:

- near-spectral residual: $\|\mathcal Tx_n-Ex_n\|<1/(n+1)\to0$;
- full-Yukawa cutoff residual: by (S2.5), $\|Y_{\rm closed}v_n-\mathrm{cut}_n(v_n)\|\le(915/916)^{n+1}\cdot916\,b\to0$ (geometric).

The two convergences share the same sequence $\{x_n\}$, not separately chosen states. **This is residual convergence**: it does not assert that $x_n$ converges in norm, nor does it call $x_\varepsilon$ an exact eigenstate.

**Direct use.** The causal, contact, positive-damping time-tail and nonlinear readings (Theorems 6.9–6.10, 6.12) consume all fields of the same preparation point; the fixity of $R$ keeps $\mathcal T$, $E$ in (4) unchanged with $n$.

**Formal correspondence.** `alpha-source/CanonicalPreparationEngineProgram.lean` (`sourceEngine`, `sourceEngine_generated`, `sourceEngine_preserves`), `CanonicalPreparationEngineCancellationForces.lean` (`sourceEngineForces_successor_zero`) and `Filtration`, `PaidForces`, `ActualRadial` with the same prefix; `CanonicalPreparationFullEnergyForm.lean` (`completeEnergyForm_split`, `actual_closed_form_complete_energy`), `CanonicalPreparationSourceRemainder.lean` (`sourceRemainder_decomposition`, `sourceRemainder_selfAdjoint`, `sourceRemainder_norm`, `sourceRemainder_readback`); `CanonicalPreparationSource{PreparedState,BoundarySequence,CausalState,NonlinearState}.lean` (`sourcePreparation_exists`, `preparationSequence_residual`, `preparationSequence_yukawa_residual`, `sourceCausalState_same_preparation`, `sourceNonlinearState_same_preparation`). Commit AB.

---

## S3 Theorem 6.9: the genuinely varying response and cutoff exchange; and the spectral measure and all-time convergence at the end of §6.9

**Objects and domain.** The carrier of Theorems 6.7–6.8, $H=H_0+Y$, the fixed $R$ and the same preparation sequence $x_\varepsilon$. A field curve means a smooth curve in the original field space parametrized by a source coordinate slice, $z\mapsto$ a point on the physical chart; the response point $q$ is as in S0.3. The cutoff index $F$ is directed by inclusion; a cutoff-order slot at a finite value $n$ is the $n$-th-order Yukawa cutoff, and at the uncut value the uncut term.

**Inputs and quantifiers.** (1)(4) for every field curve and test state; (2) for every damping $\gamma>0$ and every nonlinear parameter $r$ with $|r|\le r_*(f,\psi,p,n,\gamma)$ ($r_*$ the source-generated nonlinear radius); (3) for every $F$, every non-real $z$ and original local field neighbourhood. The two items at the end of §6.9 hold for every original core input $g$ and every bounded insertion.

**Key lemmas.**

> **Lemma S3.1 (Cutoff jet limit).** For every fixed field curve, $p$, $F$, non-real $z$ and real parameter $r$: the cutoff Yukawa jet $Y_n(p,F,r)$ converges as $n\to\infty$ to the uncut $Y_\infty$; the resolvent, current, contact, insertion and inverse contact, five items in turn, converge to the corresponding uncut operators.

*Proof.* The core fact is the **finite retainer set**: for every fixed $F$ and momentum $p$, the retained terms act only on some finite retainer index set, hence for every fixed parameter tuple $(f,p,F,z,r)$ the sequence **stabilizes pointwise**—there is an $N$ such that for $n\ge N$ the $n$-th-order jet and the uncut jet are equal as objects. An eventually constant sequence converges in its (finite-dimensional) operator space in the $\mathcal N$ neighbourhood topology, equivalently in norm—hence $Y_n\to Y_\infty$, $R_n\to R_\infty$, the current, the contact and the insertion each hold (each is a corresponding `Tendsto` declaration), except that the stabilizing order $N$ depends on the parameter tuple, not uniformly over all inputs. The resolvent limit also follows from continuity of the inverse map: for non-real $z$ the uncut moving diagonal entry is invertible and matrix inversion is continuous there. ∎

> **Lemma S3.2 (Read-back of the cutoff preparation).** For every cutoff order $n$, the $n$-th-order cutoff response equals, term by term on the original readout channel, the cutoff value of the prepared response; the response, its first derivative and its second derivative each have a pointwise identity.

*Proof.* The cutoff response's definition expands into a pairing of the completed external legs with the cutoff resolvent; Lemma S3.1 gives the convergence of each factor, and the joint continuity of the inner product transports the convergence to the reading; the derivative cases first use the same identity as a pointwise rewrite, then the convergence of the first and second jets. ∎

**Decisive derivation.**

**(1) Genuinely varying field.** The original 106-dimensional inverse and all native, coframe and retained terms generate a genuine 289-dimensional field vector and 36 curvature readings: each reading is a density integral transported along the original field curve—the actual Gauss density $Jv^{N+2}$ and the first two derivatives of the half-density ratio are transported with the curve, and the diagonal fibre keeps the graded-compression layout $\sum_gP_gP_FH_{\rm phys}P_FP_g$. The complete form and its cutoff compressions have genuine second-order jets: the native integral and the coframe integral each carry a continuous second derivative and an explicit remainder on the source domain $|r|<r_*(f,a)$, as does the composite; the inverse at a finite cutoff directly gives the same preparation's first-order $-RJR$ and complete second-order contact term.

**(2) Nonlinear response.** For damping $\gamma>0$, the nonlinear Laplace response has a genuine parameter derivative inside the source-generated radius $r_*$ (differentiable at $r=0$, with explicit derivative), and the remainder satisfies
$$\bigl\|\Phi(r)-\Phi(0)-r\Phi'(0)\bigr\|\le L^2\,\bigl(s(f,g,\psi,p,n,\gamma)\cdot m(\gamma)\bigr)\,|r|^2\,\|u\|^2,\tag{S3.1}$$
where $L$ is the external-leg bound, $s$ the source-generated remainder scale, $m(\gamma)$ the Laplace mass and $u$ the prepared image. The two independent transfer chains keep the momentum labels $p,\ p+\ell,\ p+k,\ p+k+\ell$ and the minus sign of the force, the plus sign of the contact.

**(3) From cutoff to uncut.** The original moving closed Yukawa has a dense closed graph, and the retained space and the preparation's eight external legs lie in its true domain. The literal cutoffs' 0-, 1- and 2-jets all converge to the uncut ones: this is the conjunction of Lemmas S3.1 and S3.2—first the operator convergence from the finite retainer set, then the pointwise read-back identities and the jet convergence transport the exchange to the prepared response and all 36 curvature readings.

**(4) Mother state and fixed measure.** The coordinate edges and the diagonal of the original state square recover the same mother-action state and generate all four ordered Hessian blocks; inside the source neighbourhood the moving fibre integral equals the original fixed-measure fibre exactly—the density derivatives cancel by the same transport identity (note: only the already-paid density derivative is cancelled; the response itself is read as usual)—and the mother current, the native and coframe jets and the retained balance still enter the cutoff and uncut first and second derivatives of the same preparation.

**End of §6.9: the spectral measure and all-time response of the original $H_0$.** For the original $H_0$, every original core input $g$ generates, through the same source filter, a positive finite measure $\mu_g$ on $\mathbb R$ of mass $\|g\|^2$: every finite level of the source filter gives a channel decomposition whose channel squared norms sum exactly to $\|g\|^2$, positivity and consistency are guaranteed by the projection family, and the limit measure is unique on cofinal indices. It reads simultaneously the resolvent quadratic amplitudes (Stieltjes type) of all non-real $z$ and the even-order energy moments; for nonzero $g$ the normalized probability measure has the corresponding limit statement. For every bounded insertion $A$ and damping $\mu>0$, the complete complex retarded amplitude converges in $L^1$ on the whole real frequency axis—the termwise error is controlled by the resolvent price and the mass decomposition—and through the inverse Fourier transform converges, uniformly in all times, to the time response. **These are quantities of the original $H_0$'s source response**: the positive measure is carried on the spectrum of the free generator and is not renamed as the particle spectrum of the complete interaction.

**Direct use.** The cutoff–uncut exchange of (3) is a prerequisite of Theorem 6.10's two-leg Ward and Theorem 6.12's half-axis argument; the curvature readings of (1)(4) enter the field returns of Theorems 6.11–6.13.

**Formal correspondence.** `alpha-source/CanonicalPreparationSourceNonlinearState.lean` (`preparedLaplace_derivative`, `preparedLaplace_remainder`, `sourceNonlinearState_same_preparation`), `CanonicalPreparationYukawaObservedLimit.lean` (`sourceY_limit`, `sourceResolvent_limit`, `observed_uncut_limit`, `observed_uncut_limit_near`, `observed_first_exchange`, `observed_second_exchange`, `curvature_uncut_limit`, `curvature_first_exchange`, `curvature_second_exchange`, declarations related to `finiteRetainer`), `CanonicalPreparationHalfDensityCompressionFeed.lean` (`diagonalFiber_source`, `transportedForm_fixed`, `transported_first_fixed`, `transported_second_fixed`, `compression_fixed_source`); AC adds `CanonicalPreparationSpatialFullFormFeed.lean` (`completeForm_source`, `complete_first_source`, `complete_second_source`, `nativeIntegral_fixed`, `coframeIntegral_fixed`), `CanonicalPreparationJointMixedResponse.lean` (`mixedCurvatureMatrix_generated`), `CanonicalPreparationRawJointFiveTerms.lean` (`eulerCovector_generated`, `fiveKernel_generated`), `CanonicalPreparationOriginalPreparedGreen.lean` (`original_green_equation`, `original_forced_field`), `CanonicalPreparationPhysicalFeedbackField.lean` (`physicalField_generated`). End of §6.9: `external-composite-decay/SourceHamiltonianSpectralMeasure.lean` (`actual_channel_mass`, `actual_stieltjes`, `actual_even_moment`, `actual_source_spectral_measure`, `actual_probability_limit`), `SourceBoundedInsertionTime.lean` (`actual_time_error`, `actual_uniform_time_response`). Commits AB (end of §6.9) and AC (common-field consumption).

---

## S4 Theorem 6.10: the charge–current Ward identity and one preparation

**Objects and domain.** The carrier of Theorems 6.7–6.9: the 504-mode CAR fibre, the quantum test space $\mathcal Q$, the momentum action $P(k)$, the charge action $Q_a$ ($a$ a native Lie-algebra element), the one-body spatial current $J_{\rm sp}(k,a)$ and the pair current $J_{\rm pair}(k,a)$. The two-leg responses are parametrized by the cutoff index $F$, the cutoff order $n$ and non-real $z,w$.

**Inputs and quantifiers.** (1) for every test state, every momentum $k$ and every $a$; (2) for every cutoff $(n,F)$; (3) the global-charge boundedness for every time direction, and the joint momentum representation for weighted functions on the 106-dimensional orbit.

**Key lemmas.**

> **Lemma S4.1 (The pair fibre of quantized normal order).** For arbitrary complex matrices $A,B$ (mode dimension arbitrary), the quantization map satisfies
> $$Q(A)Q(B)=Q(AB)+\Pi(A,B),\tag{S4.1}$$
> where $\Pi(A,B)=\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_k^\dagger c_l c_j$ is the pair-fibre operator; $\Pi(A,B)$ commutes with every particle-number weight operator.

*Proof.* Expand index by index and use the CAR: $c_jc_k^\dagger=\delta_{jk}-c_k^\dagger c_j$, $c_jc_l=-c_lc_j$, hence
$$Q(A)Q(B)=\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_jc_k^\dagger c_l
=\sum_{ijl}A_{ij}B_{jl}\,c_i^\dagger c_l+\sum_{ijkl}A_{ij}B_{kl}\,c_i^\dagger c_k^\dagger c_l c_j
=Q(AB)+\Pi(A,B).$$
The weight commutation holds because both $Q(A)$ and $\Pi(A,B)$ preserve occupation number. ∎

> **Lemma S4.2 (One-particle annihilation of the pair current).** On the fibre at every configuration point $z$, $J_{\rm pair}(k,a)\,f=\Pi(P_k(z),Q_a)\,f(z)$; hence $J_{\rm pair}=0$ on the one-particle projection.

*Proof.* Pointwise by Lemma S4.1: the coordinates of $P(k)Q_a f$ equal $J_{\rm sp}(k,a)f+\Pi(P_k,Q_a)f$; on the one-particle sector two annihilation operators cannot act together, so the $\Pi$ term vanishes identically. ∎

**(1) Charge–current decomposition.** Lemmas S4.1 and S4.2 directly give (6.4) of the main text: $P(k)Q_a=J_{\rm sp}(k,a)+J_{\rm pair}(k,a)$, the pair current's four-operator sum having the one-body momentum and charge matrices as coefficients, commuting with all particle-number density weights and vanishing on the one-particle projection.

**(2) Complete Ward.** The charge difference of the unprojected original physical action plus Yukawa keeps exactly four channels: configuration torque, spatial current, quartic pair current, Yukawa torque—written
$$[Q_a,H_{\rm full}]=J_{\rm cfg}(a)+J_{\rm sp}(a)+J_{\rm pair}(a)+J_{Y}(a).\tag{S4.2}$$
At every cutoff $(n,F)$, the compression defect and the Yukawa cutoff difference $Y_n-Y$ enter the remainder as they are: the finite insertion on cofinal $F$ equals
$$\mathrm{finIns}_{n,F}=W_{\rm core}+\Delta^{Y}_n(Q_a f)-Q_a\,\Delta^{Y}_n(f)+\text{compression defect},\tag{S4.3}$$
i.e. the defect is not silently deleted. The two-leg response $\langle x,R_{\rm full}(p+k,z)Q_aR_{\rm full}(p,w)y\rangle$ equals exactly the sum of the resolved channels (the core channel plus the transport remainder): resolve the two legs separately as $\widetilde x=R(p+k,z)^*x$, $\widetilde y=R(p,w)y$, first by a source-internal approximation, then read out by (S4.3); the response has the uniform price
$$\|\mathrm{resp}\|\le\|x\|\Bigl(c_a\,b_n(w)+b_n(z)\,c_a+|z-w|\,v_a(n,z,w)\Bigr)\|y\|,\tag{S4.4}$$
with $c_a$ the charge price, $b_n$ the cutoff-resolvent bound and $v_a$ the vertex price.

**(3) Global charge and one preparation.** The original 12 time directions generate from the actual action a global bounded charge $Q$: each direction's readout operator has an explicit price $c_a=\|\mathrm{quantized}(C_a)\|$. Along the same curve, the $-rQ$ variations of the bare Hamiltonian and of the retained term cancel—the complete $H$ minus the retained term produces no spurious $-rQ$ term; the joint graph of the native 106-dimensional orbit generates the weighted joint momentum representation $\sum_iP_i^\dagger(c_i f)=-Q$ (the joint readout operator is bounded, the graph closed and dense). The genuine two-leg Ward is completed by the same source filter—on cofinal $F$ the compression defect is zero and (S4.3) tends to the Ward core—and is read directly by the eight external legs and the twelve time columns of the 36 curvature readers of the same preparation point (S2).

**Boundary note.** These readings are not yet identified with the physical electromagnetic coupling, the electron or the Thomson limit; the same statement at the end of §6.10 of the main text is retained here. That the pair current vanishes on the one-particle sector is a cancellation fact, not that all currents vanish.

**Direct use.** The decomposition (6.4) and the two-leg Ward are inputs to Theorem 6.12's five-factor kernel and Theorem 6.13's static residue and cosource compatibility condition; the global charge $Q$'s price bound is consumed by Theorem 6.14's whole-word budget.

**Formal correspondence.** `alpha-source/CanonicalPreparationElectricPairCurrent.lean` (`quantized_normal_order`, `pairFiber_weight`, `full_current`, `pairCurrent_original_words`, `pairCurrent_oneParticle`), `CanonicalPreparationElectricCoreWard.lean` (`physical_full_ward`, `original_full_ward`, `finite_full_core`, `finite_full_core_eventually`, `compressionDefect_eventually`), `CanonicalPreparationElectricWeightedGraph.lean` (`weighted_adjoint_constraint`, `original_weighted_ordering`, `jointReader_price`, `original_joint_graph_closed`), `CanonicalPreparationElectricPreparedWard.lean` (`insertion_actual_channels`, `resolvedChannels_original_response`, `original_response_price`, `resolvedChannels_price`, `resolvedChannels_samefilter`, `preparedChannels_same_state`, `curvatureChannels_same_state`), `CanonicalPreparationTemporalGlobalCharge.lean` (`temporal_hamiltonian`, `temporal_contact_balance`, `globalReader_norm`). Commit AB.

---

## S5 Theorem 6.11: the mother action's second variation is this $H_{289}$

**Objects and domain.** The fixed source, the original action (3.1) and the designated solution of Construction 4.1. The 289 real directions are the real coordinates of the nine field groups (coframe, Lorentz connection, gauge, scalar, primal, independent dual etc.) on the holonomic configuration; $p\in\mathbb C^4$ are four complex momenta; $H_{289}(p)$ is the original Jacobi dictionary (3071 terms, coefficients in $\mathbb Q(\sqrt2,\sqrt{15})$).

**Inputs and quantifiers.** (1) for all variations along the 289 directions at that solution; (2) for every $p$; (3) for all 289 field unit directions; (4) for every nondegenerate coframe.

**Key lemmas.**

> **Lemma S5.1 (Smoothness and the second-order density decomposition).** The mother density is smoothly generated at the designated solution by twelve source-supported nodes (inverse coframe, third-order $H$ coefficients, the non-Abelian contact, the scalar orbit and the independent dual's third-order coefficients and adjugate matrix); its Fréchet second variation is a symmetric bilinear form and decomposes by sector—gravity (topological BF and linear $\Lambda$ residue), gauge, scalar and Dirac (including the independent dual)—into second-order densities of 234, 406, 220 and 790 terms; all 95 constants return to the original source coefficients.

> **Lemma S5.2 (Fourier merging).** Every second-order density term is a product of two field legs and one momentum monomial; the Fourier transform writes each term as two signed contributions. All 1650 terms produce 3300 signed two-leg contributions which, merged in the original dictionary's order, equal term by term the 3071 terms of the original $H_{289}(p)$; the left Euler's minus sign is inserted only once.

*Proof sketch.* The termwise comparison is an equality on finite sets, decided in two steps: the termwise equality of the two separately canonicalized term lists is decided by `decide +kernel` (the proof kernel reduces them to the same canonical term list); that the Fourier merging correctly writes each literal second-order term as signed two-leg contributions is an independent restatement theorem, composed with the term-list equality above. The coefficient field is $\mathbb Q(\sqrt2,\sqrt{15})$; scalar-coefficient equalities are decided term by term by `ring`, `norm_num` etc., not by floating-point comparison. ∎

> **Lemma S5.3 (Holonomic Euler readings).** For a holonomic configuration the Euler reading equals "partial derivative of the value minus divergence of the momentum". The pullbacks of the nine groups of mother residues along all 289 field unit directions equal that reading direction by direction: the 184 derivative-free slots give zero momentum and zero divergence, and the scalar, primal and connection direction classes (9, 24, 72) satisfy "value minus divergence equals the original Euler".

> **Lemma S5.4 (Legendre read-back).** In the Lorentz connection's complete quadratic form $\tfrac12\omega^{\mathsf T}\mathcal H\omega$, $\mathcal H$ is generated by 216 structure coefficients and a rational matrix $K_0$ of the nondegenerate coframe ($e^{\mathsf T}K_0e/\det e$); the product of the 576 polynomial entries verifies that $K$ is a two-sided inverse. After adding the spin and geometry load $J$ it eliminates uniquely to $\Omega=-KJ$ with value $-\tfrac12J^{\mathsf T}KJ-3\det e$. The Legendre transform of the coframe's 16 canonical momenta and 10 primary constraints returns the coframe kinetic energy of S1; CAR contraction over the eight Clifford directions gives the spin constant term $\tfrac{3\,\mathrm{lapse}}{4V}\mathrm{Number}-\tfrac{\mathrm{lapse}}{2V}\mathrm{normal}$; the $\mathrm{Number}^2$ term produced by pairing the linear current with the particle-number radial momentum cancels exactly against the mixed Gram's extra terms, leaving $-\tfrac{9\,\mathrm{lapse}}{8V}\mathrm{Number}$.

**Decisive derivation.** (2) obtains the source-generated decomposition of the Hessian from Lemma S5.1 and merges it by Lemma S5.2 into the same $H_{289}(p)$—the same matrix object, not an isomorphism or an approximation; (3) holds slot by slot by Lemma S5.3; (4) is a finite-dimensional quadratic elimination ($K$'s invertibility is verified by the product of Lemma S5.4) plus a finite contraction of the CAR normal order.

**Direct use.** The $H_{289}$ consumed by Theorem 6.12's Green equation, the nine compatibility residuals and the 36 curvature readers is this matrix; Theorem 6.13's static pole expands inside its source radius domain.

**Formal correspondence.** `alpha-source/CanonicalSourcePropagationOriginalHessianReturn.lean` (`nativeCompleteLiteralTerms`, `nativeHessian_complete_source`, `nativeActionFourierHessian_original`, `nativeJacobi_original`, `nativeAction_sourceField`, `nativeAction_original_regular_point`, `nativeAction_sourceField36`, `nativeAction_noetherField`, `nativeAction_noetherField36`), `CanonicalSourcePropagationPreparedMotherEulerReturn.lean` (`actualPreparedMotherEuler_generated`, `actualPreparedMotherEuler_linear`, `actualPreparedMotherEuler_multiplier`, `actualPreparedMotherEuler_{gravityAuxiliary,gaugeAuxiliary,coframe,independentDual}`, `nativeHolonomicEuler_raw`, `nativeHolonomicEuler_raw_near`, `preparedMotherForcing_cosources`). Commit AD.

---

## S6 Theorem 6.12: the same preserved current returns to $H_{289}$ through the complete half-axis

**Objects and domain.** The $H_{289}$ of Theorem 6.11 (the original Jacobi), the kernel $K_F(p)$ and the read-port $J$ of Theorems 6.9–6.10, and the response point $q$ (S0.3). The native configuration embedding of $\mathbb C^{289}$ into the configuration Hilbert space is written $\iota_{289}$ (the full-field carrier of S1; not to be confused with 6.13's five-direction embedding $E_0$). The four components of the original Green data are defined once: $D$ the contact-block inverse, $P_a$ the orthogonal projection onto the active 103-dimensional block, $K_{\rm ext}$ the extended kernel (active kernel plus empty-slot supplement), $P_{\rm null}$ the nine-dimensional null-direction projection; the row lift is written $L$ and the read-back $R_b$ ($R_bL=I$, detailed in S7). The operator pencil is of Sylvester type
$$\mathcal P_q(\lambda)A=\lambda A+\mathcal A_L A-A\mathcal A_R,\tag{S6.1}$$
with $\mathcal A_L=-iK_F(p+k)$, $\mathcal A_R=-iK_F(p)$. The Green factor matrix is written $\Xi$ (not to be confused with the cutoff index $F$): the original Green is
$$G=\Xi\,\bigl(D^{-1}+P_aK_{\rm ext}^{-1}\bigr)\,\Xi(-p)^{\mathsf T},\qquad H_{289}\,G=I-\Xi(-p)^{-\mathsf T}P_{\rm null}\Xi(-p)^{\mathsf T},\tag{S6.2}$$
the second identity holding on the regular domain where the active-103 determinant is nonzero.

**Inputs and quantifiers.** (1) for every response point, forcing and cutoff $F$; (2) for every non-real spectral parameter and $\operatorname{Re}\lambda>0$; (3)(4) for every non-real $w$, momentum $k$ and response point; (5) for every frequency with $\operatorname{Re}\lambda>0$ and one source-generated concrete instance (clock $\lambda_0=3-g$, read frequency $3$, $g$ as in (5)).

**(1) Common field and the finite-window identity.**

*Construction and quantifiers.* The same spatial half-density and the complete configuration integral generate the common field vector (289 components) and the 36 curvature readings; the field is $C^2$ in the source field curve with symmetric Hessian—each of the 36 cells consisting of 1296 mixed-response entries ($36\times36$). The mother Euler's original term is $-4W\cdot DH$, and the complete density contact term cancels by the same transport identity.

*Key derivation.* The nine-term expansion: the time derivative of the five-factor product is expanded factor by factor by the product rule and agrees term by term with the five-term time derivative kernel—the native five-term kernel and the same window's Euler covector are generated together. The finite-window identity is weighted integration by parts: for the original field curve $c(s)$ and the forcing,
$$\Xi(-\lambda,-ik)^{\mathsf T}\cdot\mathrm{forcing}
=\int\bigl(\text{time jets}\bigr)\,dt-\bigl(\text{terminal}-\text{initial}\bigr),\tag{S6.3}$$
and the derivative of the field curve equals the Green function applied to that forcing. The original Green equation (S6.2) and the forced-field equation are verified in the coefficient field by a finite matrix identity interlacing the original Jacobi, $\Xi$ and the active-103 block; the regular domain is nonempty: at a source-generated rational point, the extended kernel times the source-generated inverse matrix equals the identity (term by term by `decide +kernel`), and the right inverse gives a nonzero determinant, making that point a regular point.

*Use.* This item's Green equation also serves the compatibility criterion of 6.13(4).

**(2) The 57-term polynomial time bound and the complete positive half-axis.**

*Key lemma (graded bound).* The compressed part $C_F$ preserves the occupation grading and the retained term $A_F$ raises it by one, so the 57-th pure upgrade of $K_F=C_F+A_F$ vanishes; the Duhamel expansion terminates at order 56, and the time evolution on the full carrier is exactly the finite sum
$$\text{time bound}(\text{cutoff}\,c,t)=\sum_{n<57}\bigl(|t|\cdot\|c\|\bigr)^n\tag{S6.4}$$
—the bound of the physical time evolution is a degree-56 polynomial in $|t|$ with coefficients powers of the cutoff norm. This is the real source of the evolution polynomial bound: not a global assumption on the semigroup norm but a combinatorial truncation by the graded structure.

*Half-axis.* For every $\operatorname{Re}\lambda>0$, the polynomial bound times the Laplace weight $e^{-\lambda t}$ is termwise Bochner integrable; taking the source price $\eta=\operatorname{Re}\lambda/8$, the norm envelope $e^{(\operatorname{Re}\lambda/2)t}\cdot e^{-\operatorname{Re}\lambda t}=e^{-(\operatorname{Re}\lambda/2)t}$ gives the complete positive-half-axis forcing $\Phi^+$ and field response. The $T\to\infty$ limit of (S6.3) is the **half-axis identity**
$$\Xi(-\lambda)^{\mathsf T}\,\Phi^+=\Sigma^++B_0,\tag{S6.5a}$$
where $\Sigma^+$ is the time-jet integral term and $B_0$ the $t=0$ initial-boundary term (no longer sharing a letter with 6.13's static tensor $S$); the difference between finite window and half-axis has the explicit exponential tail
$$\bigl\|\Phi^+-\Phi_T^+\bigr\|\le\frac{2}{\operatorname{Re}\lambda}\,c\,e^{-(\operatorname{Re}\lambda)T/2},\tag{S6.5}$$
with $c$ the same source's norm price at $\eta$ ($c=\text{source price coefficient}(\eta)$), and the terminal cosource tends to zero.

**(3) Bochner inverses on the two half-planes and the spectral axis.**

*Two-sided inverses.* For $\operatorname{Re}\lambda>0$, the positive-time integral $R^+(\lambda)=\int_0^\infty e^{-\lambda t}\Phi_t\,dt$ satisfies, by the time equation $X_t'=A X_t-X_t B$ ($\Phi_t(X)=T_{p+k}(-t)XT_p(t)$), the two-sided inverse identities
$$\mathcal P_q(\lambda)\,R^+(\lambda)=R^+(\lambda)\,\mathcal P_q(\lambda)=\mathrm{id}\tag{S6.6a}$$
(the left action $\mathcal P_q(\lambda)X=\lambda X+AX-XB$ and the right action $X\mathcal P_q(\lambda)=\lambda X+XA-BX$ each follow from one integration by parts exchanging the $\lambda$ weight for a time derivative), giving the pencil's two-sided inverse on the right half-plane; for $\operatorname{Re}\lambda<0$ the negative-time (past) integral gives the left half-plane inverse symmetrically. Each open half-plane has one bounded inverse, so the pencil spectrum can lie only on the imaginary axis $\operatorname{Re}\lambda=0$.

*The spectral point at zero transfer.* At zero transfer (equal two-leg momenta), the pencil generator coincides with the single-leg generator, the identity operator lies in the kernel, and the carrier contains a nonzero unit (the same preparation's unit vector), so $0$ is an actual spectral point of the pencil; its response is exactly a $\lambda^{-1}\langle\cdot,\cdot\rangle$-type reading—unbounded at $\lambda=0$, consistent with "spectrum on the imaginary axis".

**(4) Picard iteration and the genuinely varying background.**

*Derivation.* Given a $C^1$ field history and an amplitude parameter $a$, the two legs are each driven by a nonautonomous generator $\mathcal G_a(t)$: the primal leg $U_a'= \mathcal G_aU_a$, the dual leg $V_a'=-V_a\mathcal G_a$, with initial values $U_a(0)=V_a(0)=1$; the solution exists and is unique as the evolution of a bounded generator on the finite window $[0,T_*)$ (the source window objects give the generator's uniform norm prices inside the window and a Lipschitz bound in $a$). The physical background map between the two legs (the operator-on-operators left-multiplying by $T_{p+k}(-t)$ and right-multiplying by $T_p(t)$) is **autonomous**: its generator $\mathcal E$ is a fixed transfer operator, $\mathcal E$ commutes with the map's values and the initial value is $1$, hence the map is exactly $\exp(t\mathcal E)$ (autonomous uniqueness); between the two exponentials there is the Volterra/Duhamel identity
$$e^{tL_1}=e^{tL_0}+\int_0^t e^{(t-s)L_0}(L_1-L_0)\,e^{sL_1}\,ds\tag{S6.8}$$
The amplitude derivative at $a=0$ is given by the same identity—the primal leg's variation is the variation-of-constants integral
$$\partial_aU\big|_0=T_p(t)\int_0^t T_p(-s)\,\partial_a\mathcal G_a\big|_0(s)\,T_p(s)\,ds,\tag{S6.9}$$
and the dual leg is the minus-sign conjugate form; differentiating under the integral in $a$ is paid by the parameterized-derivative lemma (on the finite window the three principal estimates—generator secant bound, evolution bound and solution amplitude bound—hold simultaneously, and dominated convergence exchanges derivative and integral). The ordered history source (the Noether history source) preserves the order of the ordered product words rather than sorting by frequency, and the first and second time derivatives of the native history kernel return term by term to that source; the mother Euler's current variants, the forcing cosources and the mother return under the varying background are generated in the same actual construction—the history return is not an approximation but a termwise equality.

**(5) The real-current operator, signal jets and the feedback fixed point.**

*The real-current continuous linear operator.* The same preparation's real current generates a continuous linear operator on the complete 289-dimensional real field: the Bochner integral $\int_0^\infty e^{-\lambda t}J_t\,dt$ of the weighted current kernel converges for $\operatorname{Re}\lambda>0$, and the difference between finite window and half-axis satisfies the same tail bound (S6.5) in operator norm; the field version has the same conclusion.

*Real Fourier signals.* The two real orthogonal components of the original four-dimensional real Fourier signal $\operatorname{Re}(e^{ip\cdot x}a)$ are each a complex-linear operator; their 0-, 1- and 2-order time jets enter the actual ordered history input and agree term by term with the mother Euler—the signal causal response reads the same preparation to the field.

*Determinant–adjugate and the unique fixed point.* The feedback matrix is $I-\mathcal U$ ($\mathcal U$ the source-generated update operator, a composite of the original Green and the five-direction residuals, not an externally supplied projection). For any $289\times289$ matrix the determinant–adjugate identity holds unconditionally; at frequencies with $\det(I-\mathcal U)\neq0$ it gives an explicit two-sided inverse, and the response equation $\varphi=f+\mathcal U\varphi$ has the unique fixed point $\varphi=(I-\mathcal U)^{-1}f$.

*The source-generated instance and the $3/16$ bound.* The source anchor takes the initial budget $B$ (source-generated bounds on the original Green norm, the time-jet matrix norm etc., $B\ge0$), the read gap $g=\frac1{8(1+B)}$, the clock $\lambda_0=3-g$ and the read frequency $3$. The genuine derivation of $3/16$: at the anchor frequency the feedback update operator splits into a Laplace-current term and an initial-value term, whose source prices give $\le\frac1{16}$ and $\le\frac18$ respectively, hence
$$\|\mathcal U\|\le\tfrac1{16}+\tfrac18=\tfrac3{16}.\tag{S6.6}$$
From $\|\mathcal U\|<1$ follows $\det(I-\mathcal U)\neq0$ (spectral radius below 1, zero kernel gives nonzero determinant), and the regular domain is nonempty; writing the response equation as $\varphi=f+\mathcal U\varphi$ gives
$$\|\varphi\|\le\|f\|+\tfrac3{16}\|\varphi\|\ \Longrightarrow\ \|\varphi\|\le\tfrac{16}{13}\|f\|.\tag{S6.7}$$
The initial cosource and the nine compatibility residuals are retained throughout.

**Direct use.** The Green equation of (1) and the zero spectral point of (3) serve directly Theorem 6.13's static pole domain, compatibility criterion and residue; the half-axis identity of (2) is consumed by 6.13(5)'s origin-weight formula; the feedback fixed point of (5) is the closed-form solution of 6.12's field feedback.

**Formal correspondence.** (1): AC `CanonicalPreparationSpatialFullFormFeed.lean` (`completeForm_source`, `transportedForm_fixed`), `CanonicalPreparationJointMixedResponse.lean` (`jointHessian_symmetric`, `mixedCurvatureMatrix_generated`), `CanonicalPreparationRawJointFiveTerms.lean` (`fiveKernel_generated`, `eulerCovector_generated`), `CanonicalPreparationOriginalPreparedGreen.lean` (`original_green_equation`, `original_forced_field`, `generatedRegularPoint`: the right-inverse identity term by term by `decide +kernel`), `CanonicalPreparationPhysicalFeedbackField.lean` (`physicalField_derivative`). (2): AD `CanonicalPhysicalLaplace.lean` (`timeBound cut t = Σ_{n<57}(|t|‖cut‖)^n`), `CanonicalPreparationPhysicalTimePolynomial.lean`, `CanonicalPreparationPhysicalSourceGrowth.lean`, `CanonicalPreparationPhysicalActualEnvelopes.lean`, `CanonicalGradedMixed.lean` (`graded_mixed_zero`, `source_homogeneous_zero`), `CanonicalPreparationPhysicalFullHalfAxis.lean` (`weighted_integrable`, `halfForcing`, `halfForcing_readback`, `halfField_equation`, `halfField_cosources`), `CanonicalPreparationPhysicalControlledFieldTail.lean` (`actual_controlled_field_tail`, `explicitSourceTail`, `source_scalarCoefficient`). (3): AD `CanonicalSourcePropagationAxisReadback.lean` (`actualResolvent_{left,right,isUnit,spectral}`, `actual_spectrum_axis`, `zero_transfer_{source_kernel,pencil_unit,resolvent_unit,prepared_pole_read,actual_spectral_point}`), `CanonicalSourcePropagationSourceSpectralInverse.lean` (`sourcePencilUnit`, finiteness of `sourcePoleSet`, `sourceSpectrum_sub_poles`), `CanonicalSourcePropagationSpectralAxis.lean`. (4): AD `CanonicalSourcePropagationActualBackgroundEvolution.lean`, `CanonicalSourcePropagationActualPreparedHistoryVariation.lean` (`historyPrimal/Dual Variation_generated`, `orderedHistoryDirection_*`), `CanonicalSourcePropagationActualNativeHistoryReturn.lean` (`actualPreparedHistoryKernel`, `actualPreparedHistorySource`). (5): AE `CanonicalPreparationSourceHalfAxisCurrentOperator.lean` (the `sourceHalfCurrent` integral, `sourceHalfCurrent_generated`, `sourceWindowJacobian` norm convergence and the $(2/\operatorname{Re}\lambda)\cdot\text{sourceCurrentPrice}\cdot e^{-(\operatorname{Re}\lambda/2)T}$ tail), `CanonicalPreparationSourceHalfAxisFieldOperator.lean`, `CanonicalPreparationSourceNativeFourierHistory.lean` (`sourceSignalOperator_{left,right}`, `sourceHistoryInput`), `CanonicalPreparationSourceOrderedSignalOperator.lean`, `CanonicalPreparationSourceSignalCausalResponse.lean`, `CanonicalPreparationSourcePreparedSignalEuler.lean`, `CanonicalPreparationSourceCurrentFeedbackAdjugate.lean` (`sourceFeedbackMatrix_actual`, `sourceFeedbackAdjugate_{left,right}`, `sourceFeedbackResolvent_{left,right}`, `sourceFeedbackResponse_{generated,unique}`), `CanonicalPreparationSourceAnalyticRegularPoint.lean` (`sourceInitialBudget`, `sourceAnchorGap` $g=1/(8(1+B))$, `sourceAnchorClock` $3-g$, `sourceAnchorUpdate_price` $\le3/16$, `sourceAnalyticResolvent_price` $\le16/13$, `sourceAnchorDenominator_ne_zero`, `sourceRegularDomain_nonempty`). Commits AC, AD, AE.

---

## S7 Theorem 6.13: poles, constraints and the static residue

**Objects and domain.** The $H_{289}$ (original Jacobi) of Theorems 6.11–6.12, the original Green $G(p)$, the Green data $L$ (row lift), $R_b$ (read-back, $R_bL=I$), $P_{\rm null}$ (the nine-dimensional null-direction projection), and the five-factor current read-port and response point $q$ of 6.12. The rest octet is indexed by eight indices $l,r$; the moving octet basis at momentum $p$ is given by the source's $4\times4$ Hermitian matrix, four states on each chirality. This section's static tensor is written $S$; the time-jet integral term of 6.12(2) is $\Sigma^+$, and the two no longer share a letter. The main text's "uncleared-field limit of a varying forcing" is carried by `actualAxisWindow_tendsto` and `axisCosource_tendsto`, `axisNullCosource_tendsto` (see the formal correspondence below).

**Inputs and quantifiers.** (1) for every three-momentum and Gauss operator $A$; (2) for every $F$, non-real $z$ and momentum pair; (3) for every $\kappa$ in the static domain (a nonempty punctured interval), forcing $f$ and the actual transfer (left momentum $-\kappa e_1$, right momentum $0$, $\lambda=0$, finite window $T$), the residue limit taken along $\kappa\to0$ inside that domain; (4)(5) for every response point, two-leg momenta, rest-state indices, $\lambda$ and finite window $T$.

**(1) The moving carrier and the overlap unitary.**

> **Lemma S7.1.** The overlap matrix $U(p)$ of the moving basis against the rest octet is unitary: the same-$\varepsilon$ preparation's orthonormality gives $U(p)^\dagger U(p)=I$, and in finite dimension the right inverse follows (there is also an explicit two-sided unitarity); $U(0)=I$. The preparation, production operators, primal legs, fibre vectors and same-$\varepsilon$ preparation at momentum $p$ are all $U(p)$ combinations of the rest ones; the readout tensor satisfies
> $$M(p_L,p_R)[A]=U(p_L)^{\dagger}\,M(0,0)[A]\,U(p_R),\tag{S7.1}$$
> i.e. the whole operator $A$ is retained and the octet only carries the outer coordinates.

*Proof.* Orthonormal columns give the left inverse; in dimension $8\times8$ a left inverse is unitary, and there is additionally a layered two-sided unitarity construction. The tensor formula comes from the bilinear expansion of the inner product at both ends: each outer coordinate picks up one $U$. ∎

**(2) Momentum-affinity and joint continuity.**

> **Lemma S7.2.** The compression $C_F(p)=C_F(0)+v_F(p)$, where $v_F$ is a continuous real-linear momentum action, so $\|C_F(p)-C_F(k)\|\le\|v_F\|\,\|p-k\|$; by the resolvent-difference formula (S0.4), $\|R_p(z)-R_k(z)\|\le|\operatorname{Im}z|^{-2}\|v_F\|\,\|p-k\|$. The finite retainer set and the retained term $A_F$ are the same across momenta, hence the joint generator, joint resolvent, joint time evolution, the 289 read-ports, the five-factor tensor and the finite Laplace window are all continuous in the momentum (each continuity declaration generated separately). No continuity of any single spectral label is assumed.

*Proof.* The momentum action is real-linear through quantization and the fixed compression, so boundedness of the velocity operator gives the Lipschitz constant $\|v_F\|$; the resolvent difference follows by taking norms on both sides of the difference formula. The retainer set depends only on the fixed retainer index set and $F$, not on $p$, hence the retained term is the same across momenta; the joint generator's momentum difference is controlled by the same velocity bound, and the time evolution, as a norm-exponential composite of the generator, stays continuous. ∎

**(3) The static pole and the residue.**

> **Lemma S7.3 (The static principal block).** At the physical momentum $p_\kappa=(0,i\kappa,0,0)$, all $\kappa$-containing dictionary terms of $H_{289}$ collect by $-\kappa^2$ into a leading term $-\kappa^2S$, with $S$ the static tensor. $S$ is explicitly invertible under the extension by the 98-dimensional complement plus the five-direction block (verified by the termwise product of the source-generated inverse list), with a source-generated norm budget; the normalized kernel is invertible inside a source-generated positive radius (a Neumann-type argument), and that radius gives the nonempty punctured static domain.

> **Lemma S7.4 (The pole decomposition).** Inside the punctured static domain, the uncleared complete 289-dimensional Green decomposes as
> $$\begin{aligned}G(\kappa)f=\ &\text{contact term}\ +\ (-\kappa^2)^{-1}\cdot V_0S^{-1}V_0^{\mathsf T}\!f\\ &+\ \text{regular part on the 98-dimensional complement},\end{aligned}\tag{S7.2}$$
> with the nine null-direction forcings retained. Each factor is continuous as $\kappa\to0$: the normalized inverse converges to the padded inverse $S^{-1}_{\rm pad}$, the effective frame converges to the native five-direction frame $V_0$, and the readout converges to $V_0^{\mathsf T}$. Hence for fixed forcing $f$,
> $$-\kappa^2\,G(\kappa)f\ \longrightarrow\ V_0S^{-1}V_0^{\mathsf T}f=:\rho_{\rm st}(f).\tag{S7.3}$$
> For a varying forcing, the same decomposition's axis window and axis cosource each have uncleared-field limits (`actualAxisWindow_tendsto` etc. in the formal correspondence).

*Proof.* The contact term and the complement term tend to zero after multiplication by $-\kappa^2$; the middle term's factors converge termwise and compose; the static domain's nonemptiness is given by Lemma S7.3's positive radius. ∎

> **Lemma S7.5 (The origin weight and the mode readout).** The five-direction origin embedding $E_0:\mathbb C^5\to\mathbb C^{289}$ (the native frame through the original change of variables) acts on the two-component vector; for the actual transfer's current, the residue is
> $$\rho_{\rm st}=E_0\Bigl(-\tfrac9{125}\sqrt{30}\,\mathfrak{w},\ -\tfrac{67}{72}\sqrt{30}\,\mathfrak{w},\,0,0,0\Bigr),\qquad \mathfrak{w}=\tfrac{3\sqrt2}{10}\bigl(J_{21}-J_{34}\bigr)=-c_{114},\tag{S7.4}$$
> where $-\tfrac9{125}\sqrt{30}$, $-\tfrac{67}{72}\sqrt{30}$ are the two exact components of $S^{-1}$ acting on the five-direction weight ($\sqrt{30}=\sqrt2\sqrt{15}$); $\mathfrak{w}$ is exactly the negative of actual cosource number 114 (see (4)), and the two gauge slots are indices $21$ and $34$.

**(4) The constraint compatibility criterion and row 114.**

> **Lemma S7.6 (Axis-field compatibility).** Applying both sides of the original Green equation (S6.2) to the actual window field:
> $$H_{289}\,\varphi=w_{\rm win}-L\,(\text{nine-dimensional axis null cosource});\tag{S7.5}$$
> hence $H_{289}\varphi=w_{\rm win}$ if and only if the nine-dimensional axis null cosource vanishes—the forward direction direct, the converse using $R_bL=I$ (read back through the original change of variables of $\Xi$). The criterion is a condition given by the theorem, not generated by it.

> **Lemma S7.7 (Constraint row 114).** Row 114 of the original read-back is a sum of three linear readings: a charge term, a covariant-constraint term and an unsupported term; the unsupported term is identically zero on the actual current window and on the half-axis. Hence actual cosource number 114 retains only the charge and covariant terms, whose Ward boundary form is in (5).

*Proof.* The equivalence of $H_{289}\varphi=w_{\rm win}$ with the vanishing of the nine-dimensional cosource is two lines of linear algebra from (S6.2) and $R_bL=I$; the threefold decomposition of row 114 is a rowwise expansion of the read-back matrix, and the unsupported term's vanishing follows from that row's termwise structure on the actual current; $\mathfrak{w}=-c_{114}$ is the rowwise equality of the actual cosource and the original large weight. ∎

**(5) The contact–deviation decomposition of the origin weight, the weighted Ward form and the price.**

*The contact–deviation decomposition.* $\mathfrak{w}$ decomposes as the native contact window minus the configuration-deviation window:
$$\begin{aligned}\mathfrak{w}&=\kappa_{\rm ct}-\delta_{\rm cf},\qquad \kappa_{\rm ct}=\int_0^T\!(\text{pole readout}\circ\text{contact kernel})\,dt,\\ \delta_{\rm cf}&=\int_0^T\!(\text{pole readout}\circ\text{deviation kernel})\,dt,\end{aligned}\tag{S7.6}$$
holding pointwise by the actual relation of the mode readout's contact and deviation kernels.

*The Laplace-weighted Ward form.* The actual cosource number 114, for every spectral parameter $\lambda$ and finite window $T$, is
$$\begin{aligned}c_{114}(\lambda,T)=\ &\int_0^Te^{-\lambda t}\,(\text{N1 colour Ward readout})\,dt\\ &+\int_0^Te^{-\lambda t}\,(\text{covariant constraint current})\,dt-\Bigl(e^{-\lambda T}Q(T)-Q(0)\Bigr),\end{aligned}\tag{S7.7}$$
the three terms corresponding respectively to (4)'s charge term (the N1 normalization agrees with the primal normalization), the covariant term and the integration-by-parts boundary; (3)'s actual transfer takes $\lambda=0$ (weight identically 1), where
$$\mathfrak{w}=\kappa_{\rm ct}-\delta_{\rm cf}=-c_{114}(0,T),\tag{S7.8}$$
i.e. the formula of the main text (5).

*Price.* The deviation window is controlled by the $|\operatorname{Im}\cdot|^{-1}$ bounds of the two matter resolvents and the operator norm of the deviation read-port $D_0F$:
$$|\mathfrak{w}-\kappa_{\rm ct}|=|\delta_{\rm cf}|\ \le\ \frac1{|\operatorname{Im}z|}\,\|D_0F\|\,\frac1{|\operatorname{Im}w|}\cdot|T|,\tag{S7.9}$$
and the residue error is further multiplied by the norm of the complete five-direction pole vector (that vector being the two nonzero component columns of $E_0$). The native residue convergence and the price hold together.

**Boundary note.** The $\kappa$ static limit and the matter Abel limit are taken separately and their order does not commute; these readings are not yet identified with the physical electromagnetic coupling, the electron or the Thomson limit.

**Direct use.** The residue formula (S7.4) and the compatibility criterion are the endpoint of §6.13; the mode kernels and the time evolution of $Q(T)$ are reused in 6.14's diffusion decomposition.

**Formal correspondence.** `alpha-source/CanonicalPreparationSource{MovingPoleCurrent,MovingPoleGaussPreparation,MovingPoleGaussVertex}.lean`, `CanonicalPreparationSourceStaticPoleDomain.lean` (`staticTensor_generated`, `paddedStaticInverse_{left,right}`, `normalizedKernel_isUnit`, `normalizedKernel_inverse_price`, `staticRadius_pos`, `staticDomain`), `CanonicalPreparationSourceStaticOriginalGreen.lean` (`staticNativeField_{uncleared,whole}`, `staticDomain_nonempty_regular`), `CanonicalPreparationSourceStaticActualPole.lean` (`staticNativeField_{pole_factor,pole_price,residue}`, `staticResidue`, `normalizedInverse_tendsto`, `nativeEffectiveFrame_tendsto`, `actualStaticField_{whole,schur,pole_price}`, `actualOriginWeight`), `CanonicalPreparationSourceModeCurrent.lean` (`sourceMode{Kernel,Current}_generated`, `actualOriginWeight_sourceReader`, `actualCurrent_staticResidue_modeReader`, `actualRestState_mode_charge_clock`, `sourceModeStatic{Coefficient,Residue}_generated`, `sourceModeHalfWeight_Abel`), `CanonicalPreparationSourceFullOriginCurrent.lean` (`fullNativeOrigin`, `actual_current_ward`, `actual_effective_dynamics`, `actual_complement_return`, `actual_native_reconstruction`, `actual_forcing_twoSectors`), `CanonicalPreparationSourceConstraint{Read,Boundary}.lean` and `CanonicalPreparationSourceColorBoundaryWard.lean` (`constraint114_source_linear`, `constraintUnsupported_actual{Window,Half}_zero`, `sourceActualCosource114_generated`, `sourceActualCosource114_actualWardBoundary`), `CanonicalPreparationSourceN1{Prepared,NormalWard,Dynamics}.lean` (`sourceActualN1Primal_*`, `sourceActualCosource114_N1WardBoundary`—the Laplace-weighted (S7.7), `actual{C,A,Generator,Time}_sourceN1_range`). The files above are byte-identical between AE and CAP, first pinned at AE.

(1)(2)'s carrier and continuity and (4)(5)'s decomposition, compatibility and price are pinned at CAP: `CanonicalPreparationSourceMovingCarrier.lean` (`movingOverlap_right_unitary` and the layered `movingOverlap_*` composites), `CanonicalPreparationSourcePreparedTensor.lean` (`sourceTensor_generated`, `actualModeTensor_{generated,same_carrier}`), `CanonicalPreparationSourceMomentumContinuation.lean` (`actualC_affine`, `actualC_difference_price`, `actualC_continuous`, `sourceResolvent_difference_price`, `sourceTime_continuous`, `sourceModeKernel_continuous`, `actualModeTensor_continuous`, `movingOverlap_zero`, `actualModeWindow_continuous`), `CanonicalPreparationSourceRetainerMomentum.lean` (`sourceRetainer_momentum`, `actualA_momentum`, `actualJoint{Generator,Resolvent,Time}_continuous`), `CanonicalPreparationSourceReaderMomentum.lean` (`rawReader_momentum_continuous`), `CanonicalPreparationSourceFullPoleTensor.lean` (`actualAxisField_{whole,residue,coupled_residue}`, `actualAxisWindow_tendsto`—the uncleared-field limit of a varying forcing), `CanonicalPreparationSourceReferenceContact.lean`, `CanonicalPreparationSourceModeNativeSymbol.lean`, `CanonicalPreparationSourceModeContactRead.lean` (`sourceContactKernel`, `sourceDeviationKernel`, `sourceActualMode_contact_deviation`—the contact–deviation pointwise relation of (S7.6), `sourceDeviationReader`), `CanonicalPreparationSource{GaussConnection,GaussKineticTorque,GaussColorWard}.lean` (the Ward identities of colour charge, covariant torque and configuration torque), `CanonicalPreparationSourceNativePoleBalance.lean` (`nativeContactWindow`, `configurationDeviationWindow`, `actualOriginWeight_native`: $\mathfrak{w}=\kappa_{\rm ct}-\delta_{\rm cf}$, `origin_native_Ward_balance`, `actualOriginWeight_residue_tendsto`), `CanonicalPreparationSourceNativePolePrice.lean` (`configurationDeviationPrice`, `actualOriginWeight_native_price`—(S7.9), `sourcePoleVector`, `actualResidue_price`), `CanonicalPreparationSourceAxisCompatibility.lean` (`actualOriginWeight_cosource114`: $\mathfrak{w}=-c_{114}$, `actualAxisField_constraint_residue`, `actualAxisField_compatibility`: $H_{289}\varphi=w_{\rm win}\iff$ the nine-dimensional axis null cosource vanishes). The original Green equation of (4) is shared with 6.12(1) at AC `CanonicalPreparationOriginalPreparedGreen.lean`'s `original_green_equation`.

Direct consumers: `alpha-source/AuditCanonicalPreparation{SharedPoleCarrier,FullPoleContinuation,PhysicalModeContact,PhysicalGaussColorTorque,PoleConstraintReturn}.lean`. Commits AE (the static and Ward main line) and CAP (moving carrier, momentum continuity, pole decomposition, compatibility and price).

---

## S8 Theorem 6.14: the matched whole-word budget and the renormalized endpoint's common tail

**Objects and domain.** The complete native-history Hamiltonian $H_0$, its finite compression $C_F=H_0-d_F$ ($d_F$ the retained term), operators on the quantum test space $\mathcal Q$ (written End), the damping parameter $\sigma=\mu>0$, and the composite-source clock $\varphi$. Two seeds $(g,\rho g)$ generate the normalized state $w$; $A=aD$ is the product of the root action and the Gauss direction, $U=a^2$; $D_c$ is the central direction; $n=\sqrt{54/125}$ is the lapse. The delayed frequency $z=\mathrm{line}(\mu,t)$ satisfies $\operatorname{Im}z\ne0$.

**Notation.** $R_3$ is the literal delayed word (the matched source word $R_{\rm forcing}$ in the source); $J_3$ is the matched price $\Pi_{m,\ell,F,z}(g)=P_3(w)+12\,\mathrm{cp}(z,w,v)/n-3\,\mathrm{contact}_{\rm cf}$, where $P_3$ is the native pressure term (a real pairing of a pair of native pressure operators on $w$, defined in Lemma S8.1) and $\mathrm{cp}$ the local clock price; $\mathrm{sh}_{40}(w)=\sum_i\|\mathrm{sh}_{40,i}w\|^2$ is the second moment of the 40-shifted columns ($\mathrm{sh}_{40,i}$ the shifted-column operators); $\mathsf{sc},\mathsf{cf}$ are respectively the scalar form and the coframe Gram; $M_\mu(k)$ is the source $\mu$-factor, $P_\rho$ the radius price, $C_{\rm J}$ the closed joint cost, $\mathcal E$ the renormalized endpoint and $R_{\rm df}$ the diffusion remainder.

**Inputs and quantifiers.** (1) for all $m,\ell,F$, non-real $z$ and domain elements $g$; (2) for every $\varepsilon>0$, $\mu>0$ and domain elements $g,k$, there is an $N$ such that all $m\ge N$, $\ell\ge m$, cofinal $F$ and **both** sharp cutoffs (one boolean choice, two values) hold uniformly; (3) the same quantifiers as (2) but with the object replaced by the absolute endpoint integral, over the two causal ports (one boolean choice); (4) on cofinal $F$ for all $m,\ell,z,g$.

**Key lemmas.**

> **Lemma S8.1 (The matched positive source).** Write the matched column $C_3:=UD+3iD_cU$ ($D_c$ the central direction) and the native pressure term
> $$P_3(f)=\operatorname{Re}\bigl\langle f,\bigl([A,[A,H_0]]+3U[D,H_0]+2U\,M_{\rm matter}+\tfrac85U\,V_{\rm vac}\bigr)f\bigr\rangle.\tag{S8.0}$$
> The tester identity, the exact phase correction and the slotwise lower bound hold together:
> $$\mathcal T:=C_3+2U=UD+3iD_cU+2U=UD+i\,U\bigl(3D_c+4i\bigr),\qquad J_3=R_3+6\,\sigma\,\operatorname{Im}\langle C_3w,w\rangle,\tag{S8.1}$$
> $$J_3\ \ge\ \tfrac{3n}{8}\|C_3w\|^2+\tfrac{5n}{2}\mathsf{sc}(Uw)+10n\,\mathrm{sh}_{40}(w)+\tfrac{3n}{4}\mathsf{cf}(Uw)+18n\|w\|^2,\tag{S8.2}$$
> every right-hand slot nonnegative, and $P_3(w)\le4J_3$.

*Proof sketch.* The tester's two forms are interchangeable through the commutation relation $D_cU-UD_c=2iU$ (the inverse-expansion relation), a finite operator identity; the phase correction is the termwise expansion of $J_3-R_3$ (the merging of the pressure term with the $U$ cross terms, substituting $D$'s generator commutation relation); the lower bound is the matched slot expansion: the local clock price's lower bound, the nonnegativity of the scalar form and the coframe Gram, the shift moment and the state energy term by term nonnegative. $P_3\le4J_3$ is a corollary of the same slot expansion: the pressure term is controlled by four times the clock-price and Gram slots. ∎

> **Lemma S8.2 (Common phase payment).** For $\mu>0$, $g$ and every $\varepsilon>0$, there is an $N$ such that all $m\ge N$, $\ell\ge m$, cofinal $F$ and the two causal ports satisfy
> $$\int_{\mathbb R}\bigl(J_3-2R_3\bigr)_+\,dt\ \le\varepsilon\tag{S8.3}$$
> This is a **positive-part** integral, not an absolute-value bound: only the side $J_3>2R_3$ is paid—the intervals where $J_3-2R_3$ is negative incur no liability (the exact form is $\int^{-}\mathrm{ofReal}(J_3-2R_3)\le\varepsilon$). The absorption chain: by (S8.1) exactly $J_3-2R_3=12\sigma\operatorname{Im}\langle C_3w,w\rangle-J_3$ ($\sigma=\operatorname{Im}z$, and on the actual frequency $\sigma=\mu$); the phase price inequality (Cauchy–Schwarz then Young, taking $t=\eta\cdot3n/8$ and using the slot $\tfrac{3n}{8}\|C_3w\|^2\le J_3$ of (S8.2)) gives
> $$\bigl|6\sigma\operatorname{Im}\langle C_3w,w\rangle\bigr|\ \le\ \eta J_3+\frac{24\sigma^2}{n\eta}\|w\|^2;$$
> taking $\eta=\tfrac12$ gives $J_3-2R_3\le2\bigl|6\sigma\operatorname{Im}\langle C_3w,w\rangle\bigr|-J_3\le\tfrac{96\sigma^2}{n}\|w\|^2$, so the positive-part integrand is controlled by $K\cdot$(normalized state energy), $K=96\mu^2/n$; the normalized response's ordinary common tail, at target $\varepsilon/(K+1)$, gives the same $N$ and pays both phases at once.

> **Lemma S8.3 (Radius budget).** The radius-square decomposition
> $$\rho^2=1+\tfrac{2\|\mathrm{vac}\|^2}{25}+\tfrac12\|\varphi-\tfrac{2\mathrm{vac}}5\|^2-\tfrac14\|\varphi-\tfrac{4\mathrm{vac}}5\|^2\tag{S8.4}$$
> gives
> $$\|v_\varphi\|^2\le\Bigl(1+\tfrac{2\|\mathrm{vac}\|^2}{25}\Bigr)\|w\|^2+\frac{J_3}{20n}.\tag{S8.5}$$

*Proof.* The $\|\varphi-\tfrac{4\mathrm{vac}}5\|^2$ term is paid by the $10n\,\mathrm{sh}_{40}(w)$ slot: $10n\,\mathrm{sh}_{40}\le J_3$ (all slots of (S8.2) nonnegative), so $\tfrac12\mathrm{sh}_{40}\le J_3/(20n)$, substituted into the radius identity. ∎

> **Lemma S8.4 (The endpoint common tail).** The renormalized second Green endpoint
> $$\mathcal E=\operatorname{Re}\langle k,(H_0-\operatorname{Re}z)Aw\rangle-\|k\|^2\operatorname{Re}(1/z)\tag{S8.6}$$
> reads on cofinal $F$ only two original $H_0^2g_i$ inputs (a fixed endpoint word); its absolute whole-frequency $L^1$ tail has a common $N$: $\int|\mathcal E|\,d\omega\le\varepsilon$, holding for both causal ports at once. The derivation has two halves: the fixed-frequency price satisfies the source-generated bound
> $$\mathrm{fixPrice}(m,\ell,\mu,\eta)\ \le\ 4\eta\cdot\frac{\pi}{\mu}+C(\mu,\eta,g)\cdot\Sigma,\tag{S8.7a}$$
> where $\frac{\pi}{\mu}=\int_{\mathbb R}\frac{dt}{t^2+\mu^2}$ is the mass of the Lorentz-type kernel (the coefficients $\frac{\pi}{4\eta\mu^3}+\frac{\pi}{4\eta\mu}$ times second-order source masses enter $C$) and $\Sigma$ is a sum of fixed-source squared norms. Taking $\eta=\varepsilon\mu/(8\pi)$ gives $4\eta\cdot\frac{\pi}{\mu}=\frac{\varepsilon}{2}$; then the source's fourth-order jets and the Ritt third- and fourth-order gradient bounds (constants 32, 256) press $\Sigma$ below $\varepsilon/(2(C+1))$, hence $C\Sigma\le\varepsilon/2$ and the total $\varepsilon$.

> **Lemma S8.5 (Diffusion covariance).** The diffusion flow $\Gamma_L(X)=\mathcal D^{\mathsf T}X+X\mathcal D-2AXA$ ($\mathcal D=A^2-3D_{\rm clk}$, $D_{\rm clk}$ the drift-clock operator) satisfies
> $$\Gamma_L(1)=0,\qquad \Gamma_L(V)=18\cdot1\tag{S8.7}$$
> ($V$ the volume action, $VU=I$); the noise kernel $K_t(x,y)=2\int_0^t\rho_s(x)\rho_s(y)\,ds$, $\rho_s=(V(x)+18\max(s,0))^{-1/2}$, is positive definite for every finite point family; the carré retains the complete cross:
> $$\Gamma_L(X^2)-\Gamma_L(X)X-X\Gamma_L(X)\big|_{X=H_0}\ =\ 2\,\|[A,C_F]f+[A,d_F]f\|^2.\tag{S8.8}$$
> The regularized deviation $\|A-\mathcal D_t\|^2$ has a common payment $(192t/n)J_3$ and, under the same quantifiers, a whole-frequency tail.

**Decisive derivation.** (1) is Lemma S8.1. (2) combines three budgets: the radius-response price budget under a sharp cutoff ($C_{\rm J}\le\varepsilon/2+C\cdot(\text{homogeneous term}+4\,\text{phase budget})$), the homogeneous radius budget ($\delta$) and the common phase payment ($\delta$, whose $\varphi$-response budget has the form $\delta+2(\mu/(20n))\int R_3^{\,+}$); the phase error is converted, through Lemma S8.3's $J_3/(20n)$ factor, into the matched word's positive-part integral $\int R_3^{\,+}:=\int(R_3)_+\,dt$ (the source form $\int^{-}\mathrm{ofReal}\,R_3$), with coefficient
$$C\cdot5\delta+4C\cdot\bigl(2\,\mu/(20n)\bigr)\cdot\int R_3^{\,+}\ \longrightarrow\ \varepsilon+48\,M_\mu(k)\,P_\rho\,\frac{\mu}{20n}\int R_3^{\,+}\tag{S8.9}$$
(taking $\delta=\varepsilon/(10(C+1))$ and $C=6M_\mu(k)P_\rho$, the coefficient identity $4C\cdot2\mu/(20n)=48M_\mu(k)P_\rho\cdot\mu/(20n)$ is checked term by term: $4\times6\times2=48$, agreeing with the right-hand side of `actual_original_native_matched_Gamma_budget`). (3) is Lemma S8.4. (4) is Lemma S8.5 and the literal expansion: on cofinal $F$,
$$R_3=\frac{\mathcal E}{\sigma^2}-\frac{D_{\rm ren}}{2\sigma^2}+R_{\rm df},\qquad D_{\rm ren}=W_{C_F}^{(2)}-2\|v_{\rm fix}\|^2\operatorname{Re}(1/z),\tag{S8.10}$$
where $W_{C_F}^{(2)}$ is the second-order $C_F$ word and $v_{\rm fix}$ the fixed column. The same family's diffusion-source price is, through the phase identity, exactly the matched price: $\Pi_{\rm df}=R_3+6\sigma\operatorname{Im}\langle C_3w,w\rangle=J_3$ (i.e. the electric-word form $W_{\rm elec}+6\sigma\operatorname{Im}\langle C_3w,w\rangle$), not $R_3$ itself.

**Boundary note.** (2) is a budget for the two prescribed sharp cutoffs and the original source responsibility, not a statement about the complete $C_F$ semigroup; $D_{\rm ren}$ and $R_{\rm df}$ are the parts of $R_3$ settled by their own consumers.

**Direct use.** The matched price of (1) is the common balance of (2)(4); the endpoint tail (3) gives the positive measure of the end of §6.9 a corresponding whole-frequency convergence on the composite-source clock.

**Formal correspondence.** `external-composite-decay/SourceClockPhiNativeMatchedSource.lean` (`matchedColumn`, `matchedTester`, `matchedPrice`, `matchedForcingWord`, `actual_native_matched_source`, `actual_native_matched_common_payment`), `SourceClockPhiNativeMatchedGammaBudget.lean` (`radius_shifted_norm`, `actual_original_native_matched_radius_budget`, `matchedBudget`, `actual_original_native_matched_Gamma_budget`), `SourceClockPhiRenormalizedSecondGreen{,Tail}.lean` (`renormalizedEndpoint`, `actual_renormalized_fixed_source`, `actual_renormalized_endpoint_absolute_common_tail`), `SourceClockPhiMatchedDiffusionSource.lean` (`diffusionDrift`, `diffusionCurrent`, `noiseKernel`, `diffusionRemainder`, `original_matched_diffusion_covariance`, `fixedEndpointWord`, `actual_matched_diffusion_source`), `SourceClockPhiFixedSourceJets.lean`, `SourceClockPhiRittHigherGradient.lean`. Commit AE; the original geometric bulk time budget `SourceGeometricBulkTimeBudget.lean` (`actual_original_geometric_budget`), used in the dependency closure through `SourceScalarEssentialBudget.lean`, is not in the AE commit, and its bytes are kept at Homework `fa15016c…` (see Appendix D.7 of the main text).

---

## S9 Propositions 9.1–9.3 and the public-experiment evidence of §9.2

Each item states its evidence class separately, following the three classes of Table 4 of the main text: **mathematics** (a source-internal formal theorem, with proof); **dual-implementation check** (two programs sharing no forward computation, each producing a frozen first receipt, then cross-checked); **statistical contract** (an anytime test with a pre-registered error budget, with statistic, budget and criterion given). Historical numbers not marked inside an item keep their original frozen identities of §9.2; this section re-runs no event stream or fit.

### S9.1 Proposition 9.1: the complete optical source domain and the joint 95% strictly positive CH

**Objects and domain.** The conditional source family of the NIST 2015 public counts: coordinates $(m,z,x,r,e)$ describe the same two-polarization TMSV, a common real Jones frame and scalar losses; $k=(1-2\lambda)T$ keeps the per-pulse phase mixture; the training data are six confidence intervals (four single, two joint).

**(1) Complete source (mathematics).**

> **Proposition S9.1a (Phase fibre).** The common sign constant $k$, the physical square bounds and all training slabs of a lawful original source hold if and only if there is a lawful phase $\lambda$ and a snapshot—generated inside the original source and a lawful $k$, not supplied by the caller.
>
> *Proof sketch.* The two directions of the "if and only if" are elimination and reconstruction: the forward translates the training intervals into linear constraints and square bounds on $k$; the reverse solves $\lambda=(1-k/T)/2$ back from $k$ and checks term by term that this $\lambda$ lands in the original lawful domain, every cell count of the snapshot generated by the same source. ∎

> **Proposition S9.1b (Mean map).** Four actual means recover the common covariance coordinates $(m,z,x,r)$; all single intervals hold if and only if the intersection of eight half-spaces does. Strict ascending ordering generates $z>0$, $R^2>0$.
>
> *Proof sketch.* The four means are linear readouts of the coordinates, invertibility given by the explicit nonzero determinant of the coefficient matrix; each single interval is a pair of half-spaces on the coordinates, four giving eight. ∎

> **Proposition S9.1c (Covariance source).** Every regular quintuple ($z>0$) and lawful $k$ generate by themselves an $\arctan$ common axis, the original RawSource and a lawful phase, and read back exactly the five coordinates and all cell/five-pulse windows; the pure-mode boundary $n_V=0$, $T=0$ and all $\lambda$ readouts are equivalently retained.
>
> *Proof sketch.* The axis is generated from $(x,r)$ by $\arctan$; $T$ and the two intensities are recovered from $m,z$ and the transmission relation; the read-back is a coordinatewise algebraic identity. ∎

**(2) Ports and infinite Born (mathematics).**

> **Proposition S9.1d (Environment ports).** The actual polarization action preserves $\mathrm{Pol}\otimes\mathrm{Env}$; the six ports generate, for every $T_H,T_V\in[0,1]$ and $|\xi|\le1$, the effect $\Gamma_n=O^\dagger X^{\otimes n}O$ of every $n$; $\xi=1$ recovers the original $\Gamma$ of all $n$; the two environment components cannot be replaced by the old occupation $\Gamma(R)$.
>
> *Proof sketch.* The port action is a native symbol realization of the two-mode unitary; $\Gamma_n$ is a blockwise identity per occupation number, positivity given by the effect as a compression; substituting $\xi=1$ gives the original $\Gamma$. ∎

> **Proposition S9.1e (Matched infinite Born).** The complete infinite Born joint probability in the matched case is
> $$Q_{AB}=\frac{1}{1+n_V\,(T_A+T_B-T_AT_B)}.\tag{S9.1}$$
>
> *Proof sketch.* The per-sector Born terms are generated by the actual source root and $D$ (keeping the complex phase and the sector mass budgets), summing over all $n$ is a geometric series whose denominator is $1+n_V(T_A+T_B-T_AT_B)$. ∎

**(3) Statistical fibre and members of both signs (dual-implementation check).** Each of the six training intervals may vary inside its complete interval; two independent covering trees (primary and independent implementations) each recompute term by term **81,922 nodes**, paying the initial whole domain, the outerness of every interval contraction, the complete partition, the exclusion grounds and all capped and boundary segments—the primary retains 15,061 blocks, the independent 11. The 512 members are each reborn from the native recipe: the primary's 256 Gaussian envelopes all contained, the independent's 256 actual Born envelopes all contained; **141 actual Born out-of-bounds counterexamples** (47 primary, 94 independent) uniformly include the held-out cells—for example the independent member no. 6's $j_{01}\approx0.00016726781197301952$ lies strictly above the original upper bound $0.00016712361973910759$; these sources satisfy all six training CIs, so the training constraints do not imply all held-out cells fall inside the bands, while the whole source family is not rejected.

On the all-data intersection $F_{\rm all}=F_{\rm train}\cap$ all public held-out CIs of the twelve CIs, the acceptance of another 81,922 nodes and 128 members gives: on every path **64 actual $\Gamma$/Fock sources** satisfy all twelve exact CIs with the complete outcomes, among them **41 strictly positive CH and 23 strictly negative CH**; concrete sign witnesses refute uniform strict positivity and uniform strict negativity over the whole $F_{\rm all}$ (the domain's sign certificate is registered as mixed of the two numbers). **This is a retrospective check of a conditionally consistent source family, not an identification of the actual apparatus configuration, and not a blind-state verification.**

**(4) Joint 95% domain (statistical contract plus mathematical kernel).** Inside the original $1/20$ joint budget, the actual setting exposures, all four outcomes and the source-generated exact normalized support function are additionally consumed:
$$h=\ell\cdot\mathrm{CH}-\varepsilon(1-\varepsilon)\min(c^{A}_{01},c^{B}_{10},c_{11}),\qquad d_k=1+2^{-k}h,$$
$$\log E_k=W_{\rm obs}\log a_k+L_{\rm obs}\log b_k-T\log d_k.\tag{S9.2}$$
where $c^{A}_{01}$, $c^{B}_{10}$, $c_{11}$ are respectively the A-side 01, B-side 10 and joint 11 outcome counts. The safe old failure bound is $3/(80\times32767)$; the total budget $1/20$ minus that failure bound is divided equally among the 24 complete-exposure contrast families and the $24\times4\times6\times40$ conditional-direction bets. The source kernel generates by itself the exact support vertices, the positivity of $d_k$ and the one-step expectation bound (`NormalizedSourceBet.lean`); the statistical cross certificates check term by term the 576 new intervals, 23,040 direction bets, 480 original fixed-bet base values and 24 rational inversion brackets. The new joint 95% acceptance domain is nonempty: **8 original $\Gamma$/Fock physical members** satisfy simultaneously the old 72 CIs, the new 96 conditional constraints and the four joint source cuts, the complete continuous outer cover holds, and **every** accepted source satisfies
$$\mathrm{CH}_{N5}>1.3790180504\times10^{-6}\tag{S9.3}$$
(the exact rational lower bound is kept by the certificate; the two statistical heads were frozen at `5a35416ec6` and `85d5b45efa`).

**(5) Public review (statistical contract).** The family upper bound of the 24 public spacelike source-signature families at $\alpha=0.05$ is approximately $0.00241643$; the whole continuous nominal domain of the named environment-calibration nominal model and the original confidence interval are strictly disjoint; the five published controls of the nineteen r6/r6.1 sources all deviate (that verdict keeps its original contract identity and is not reinterpreted as a new Bell count test).

**Direct use.** The source domain and ports of (1)(2) are the source kernel of the observation-generated slice of §9.2; the members and acceptance domain of (3)(4) are cited directly by Proposition 9.1 of the main text; (5) is the public-review entry of §9.2.

**Formal correspondence.** AD: `nist-real/nominal-replay/observable-closure/full-statistical-fiber/` (`PhaseFiber.lean`, `TrainingChart.lean`, `CovarianceSource.lean`, `CovarianceSourceCertification.lean`, `PhaseCertification.lean`; check receipts `cross-verification.json`, `all-data-verification.json`, `all-data-sign-certification.json`, `criterion.md`, `criterion-all-data.md`), `environment-source/` (`MatchedSource.lean`, `EnvironmentSource.lean`, `SectorSource.lean`; `criterion.md`), `public-review/source-compression/` (`NormalizedSourceBet.lean`; receipts `statistics-cross-verification.json`, `kernel-certification-first.json`, `domain-verification.json`, `source-compression-verification.json`) and `public-review/` (`complete-review*.json`). Commit AD. This writing re-ran no covering, member generation or statistical acceptance.

### S9.2 The remaining NIST/Storz public-experiment results of §9.2

**(a) The Storz nominal lock (existing frozen statistical contract).** The first 100000 trial rows of the ETH data [8,9] are read under the frozen rule; at $\alpha=0.025$ the zero-radius model is rejected: maximal $\log E=46803.6234$, the independent high-precision receipt $p_{\rm any}\approx2.783760711\times10^{-20327}$ (the `0.0` of the original JSON is a floating-point underflow). Radii $0.01,0.02,0.05$ are still rejected, $0.1,0.2$ not rejected. The phase-bridge gap (substituting the control map into the original CHSH sign definition gives $S=0$) keeps the standalone verdict on the underlying source theory **inconclusive**.

**(b) The NIST nominal replay r0003 (dual-implementation check).** The nominal model follows the frozen choices of §9.2 (the normalized $|HH\rangle+r|VV\rangle$ family, mirrored angles, efficiency-product joint counts, per-trial background, CH-type combination); the efficiency half-width was frozen beforehand at probability $0.003$. The numerical optima of the centre and 16 corners form the pre-declared band, widened by $\pm0.05^\circ$, $\pm0.0005$ to
$$r\in[0.3051567847356201,0.3257119970321657],\quad \theta_0\in[4.727559269219637^\circ,5.179646420478821^\circ],$$
$$\theta_1\in[-27.552833724021912^\circ,-26.90090064406395^\circ].\tag{S9.4}$$
The centre is $(0.315463895,\,4.954737358^\circ,\,-27.232869633^\circ)$. The five documented values $r=0.2872$, $\theta_0=4.2^\circ$, $\theta_1=-25.9^\circ$ and the two Bob mirror angles all lie outside the band (the primary implementation's verdict `REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND`, the independent implementation the same). This is an optimality-band verdict on the nominal model under frozen inputs, not a new Bell event test, and it does not undo the original experiment's conclusion.

**(c) The Table S-II conditional source member (dual-implementation check).** On the four-cell full counts (five-pulse window, $N=177{,}358{,}351$, no-click outcomes kept), a full-Fock source is trained on cells 00, 01, 11 with the fourth cell held out: all 12 probability envelopes lie inside the simultaneous average-probability domain—a conditionally consistent member on public counts, not an identification of the actual apparatus configuration.

**(d) The AC observation-generated source slice and the two-Bob-angle update (dual-implementation check plus Lean consumers).** The revised slice takes only the four single and joint00 centres from cells 00 and 11, restores the original confidence interval for joint11, and holds out the two complete cells 01 and 10. The two independent covering constructions each produce **69 segments**: 32 entirely lawful, 35 exclusions and 2 boundaries, 68 partition cuts, no missing or repeated segments, no capped segment. The lawful outer interval $\eta_A\in[0.7411896212237604,\,0.7414274323892578]$; the canonical rational member $\eta_B\approx0.76465288593$, $\lambda\approx0.00409579367$, and the 12 mathematical probabilities of the two canonical members all lie inside the original CIs; the whole slice's prediction envelopes for the two held-out cells also fall inside the held-out CIs:
$$\text{01}:\,[0.00015821397237,\,0.00015855716089],\qquad \text{10}:\,[0.00015026944774,\,0.00015053199993].\tag{S9.5}$$
Keeping the same source and training phase, the two independent derivative systems give a strict finite update that **lowers both Bob angles by $0.01^\circ$** over the entire rounding box of $\pm0.05^\circ$ at the four angles (update angles $(4.2,-25.9,-4.21,25.89)$, common direction, step $1/100$ degree): the primary implementation's common gain lower bound $\approx1.99\times10^{-9}$, the independent implementation's $\approx1.69\times10^{-9}$, the independent Fock endpoint gain $\approx3.8493\times10^{-9}$. The Lean consumers (`ObservableClosure.lean`, `ClosureConsumer.lean`, `ScalarFiber.lean`, `ScalarFiberConsumer.lean`) read the slice back as source-family objects. **This is a conditional-consistency result on one named one-dimensional slice**: it claims no complete six-dimensional statistical fibre, identifies no actual hardware driver, and recovers no apparatus optimum.

**Formal correspondence.** AB: `nist-real/nominal-replay/{criterion-r0003.md,replay-r0003.json,independent_replay-r0003.json}`; AC: `observable-closure/{criterion-ef0002.md,verification.json,slice-primary.json,independent-slice.json,cross-receipt.json,receiver-criterion.md,receiver-verification.json}` and the four Lean consumers (above). Commits AB, AC.

### S9.3 Proposition 9.2: zero-empirical-input prediction, the complete atomic readout domain and same-law parameters

**Objects and domain.** The readout model of the atomic Bell experiment of Rosenfeld et al. [11]: Bloch probes are parametrized by $(\mu,u,z)$—$\mu$ the gain, $u$ the Bloch-vector part, $z$ the bias; effects $E_\pm$, probabilities $\Pr_\pm$; XZ axis settings.

**(1) Prediction lock (mathematics).**

> **Proposition S9.3a.** The original source generates, for all lawful XZ axes, probability families with the uniform bound $|S_{\rm CHSH}|\le2\sqrt2$; fixed orthogonal axes and a normalized bisector generate a 32-cell exact prediction reaching $2\sqrt2$. The constructor contains no data, device or calibration parameters.
>
> *Proof sketch.* The actual proof of the upper bound is explicit Cauchy–Schwarz: writing $S_{\rm CHSH}$ as the inner product of two four-vectors $u=(\pm a_0^x,a_0^z,a_1^x,\pm a_1^z)$ and $v=(b_0^x+b_1^x,b_0^z+b_1^z,b_0^x-b_1^x,b_0^z-b_1^z)$, the unitarity of the two axes gives $\|u\|^2=2$, $\|v\|^2=4$, hence $S_{\rm CHSH}^2\le8$, and taking the root $|S_{\rm CHSH}|\le2\sqrt2$ (uniform over the two herald signs). The 32-cell prediction is a per-cell algebraic value for four outcomes × two stations × four settings, satisfying normalization, nonnegativity, $\tfrac12$ marginals and the alignment; reaching $2\sqrt2$ is a cell-by-cell substitution of the fixed axes (diagonal directions $\pm1/\sqrt2$) into the CHSH formula. ∎

**(2) Complete readout domain (mathematics).**

> **Proposition S9.3b (Round trip).** Every lawful binary readout channel (including negative or zero gain) and XZ axis generates a compact effect $(\mu,u,z)$; conversely, the radius and the source cone generate a lawful channel and axis, and the round trip is exact; four effects give the complete domain of 12 real coordinates.
>
> *Proof sketch.* The forward is the Bloch decomposition of the effect matrix (compactness given by coefficient bounds); the reverse—the radius condition guarantees the constructed matrix is a lawful quantum effect and the source-cone condition guarantees the axis is lawful; the two-way composite is a componentwise identity. ∎

**(3) All trials (statistical contract).** The 10,201 and 10,202 valid pairs of the two Munich runs keep the original order; the test is the prefix-maximal likelihood ratio (anytime $e$-value) against the ideal zero-error surface: April is rejected at prefix **3974**, where it first crosses threshold 40 (maximal $E\approx494.849935$); the complete readout domain has one exact original witness in each run, and all 20,403 prefixes stay strictly below 40 (April maximum 1, June approximately 1.338729277); the two runs share a $1/20$ anytime budget.

**(4) Same law and fibre (mathematics).**

> **Proposition S9.3c.** Two lawful setting families give the same probability law if and only if the four biases and the two groups of X/Z product matrices agree—the maximal observational quotient of the whole domain; inside the regular range, a same-law effect is exactly a lawful reciprocal scale of one unique nonzero $(s,t)$.
>
> *Proof sketch.* "Only if": the probability equality holding on all inputs forces the two families' coordinatewise readouts to be equal—the biases are read from the constant terms, the product matrices from the quadratic terms; "if": the same parameters generate the same law. The actual structure of the scale: regularity gives $a_0^u b_0^u\neq0$ and $a_0^z b_0^z\neq0$, and the product-matrix equality, through a rank-one decomposition (rowwise/columnwise factorization with nonzero anchors), writes all $u$ coordinates of the other side as $s$-multiples and all $z$ coordinates as $t$-multiples, the opposite direction by $1/s,1/t$; the target effect is lawful if and only if $(s,t)$ satisfies the source cone's lawful-scale condition, in which case the other family is generated exactly by the scale transformation; the scale is unique—$s$, $t$ are recovered explicitly as ratios of the regular anchor coordinates, and any $(s',t')$ generating the same family must equal them. Hence inside the regular range, **every same-law effect is a lawful reciprocal scale of some unique nonzero $(s,t)$**. ∎

**(5) Response bounds (mathematics plus dual-implementation check).** Over the entire original confidence domain all effective gains are at least $0.36579$, and both kinds of gauge error rates are below $0.37916$: the bounds are given by the source-internal response formulas (the mathematical part), and the pointwise check over the whole confidence domain is done by the two independent implementations (the dual-implementation check).

**Direct use.** The readout domain of (2) and the same-law quotient of (4) are the whole input of Proposition 9.3; the witness domain of (3) is consumed by 9.3(1)'s joint gain upper bounds.

**Formal correspondence.** `Bell/TheoryBlind.lean` (prediction lock, CHSH bound, 32 cells), `Bell/ReadoutEffects.lean` (effect round trip), `Bell/ReadoutIdentification.lean` (same law, fibre, unique scale), `Bell/ReadoutResponseBounds.lean` (response bounds); `munich/` (`README.md`, `criterion-mu0001.1.md` and `readout-domain/`'s `parameter-recovery.md`, `history-source.md`, `verification.json`, `identification-verification.json`, `response-projection-verification.json` etc.). Commits AD (Lean entries), AE (Munich consumers).

### S9.4 Proposition 9.3: the hardware inverse, the pulse-realizable image and the original post-measurement history

**Objects and domain.** The same readout domain as S9.3; the detector effect $E_{\rm click}=dI+kJ$, $k=(1-d)\eta$; Garthoff's original 12-state matrices, 18 natural transitions and 7 ionization channels generate the GKSL dynamics; finite rectangular pulses.

**(1) Joint gain upper bounds (dual-implementation check).** The same whole-prefix joint domain gives 8 cross-setting gain product upper bounds and 6 maximal-ray bounds: April's maximal gain $>0.67020$, each side $>0.44918$; June's $>0.66386$, $>0.44071$ respectively. The two implementations each produced a frozen first receipt and the cross-checks agree.

**(2) Two-probe unique inverse (mathematics).**

> **Proposition S9.4a.** On the identified regular complete law, the signed responses to two source-known independent Bloch probes and a nonzero identification determinant give two-sided inverses, recover all family coordinates, and the effect family is unique; the probes may come from different settings, and zero determinant has a separate counterexample.
>
> *Proof sketch.* Probe responses are linear readouts of the family coordinates; when the two-probe response matrix has nonzero determinant, Cramer's rule gives two-sided inverses and recovers the coordinates term by term; uniqueness follows since any same-law effect gives the same response, and the inverse image is unique. At zero determinant the linear system is underdetermined, and an explicit counterexample gives two families sharing all responses. ∎

**Boundary note.** The two-probe unique inverse needs independently prepared probe inputs; the nominal settings and AOM channel identities of the original 2021 thesis [13] do not pay that input.

**(3) Detector fibre (mathematics).**

> **Proposition S9.4b.** $E_{\rm click}=dI+kJ$, $k=(1-d)\eta$; for positive gain, all lawful $(d,k)$ satisfy exactly
> $$0\le d\le m,\qquad M-d\le k\le1-d,\tag{S9.6}$$
> where $m=(1-\mu-g)/2$ and $M=(1-\mu+g)/2$ are the effect's minimum and maximum click probabilities; the inverse atom is unique, and $\eta\,\lambda_{\max}(J)\ge\dfrac{2g}{1+\mu+g}$.
>
> *Proof sketch.* The bound on $d$ is the physical range of the dark-count rate; the two-sided bound on $k$ is the eigenvalue-by-eigenvalue translation of the effect condition $0\le E_{\rm click}\le I$ on the spectrum of $J$—the spectral minimum gives the lower bound $M-d$, the maximum $1-d$; the inverse atom is unique because the Bloch expansion coefficients of $E$ recover $(d,k,J)$ uniquely; the efficiency lower bound follows by substituting $\eta=k/(1-d)$ into the spectral-end condition and rearranging. ∎

**(4) Atomic forward and pulse image (mathematics plus dual-implementation numerical forward).** This item has two evidence classes, stated separately and not merged.

*Mathematics (source-internal Lean theorems).*
> **Proposition S9.4c (Realizability characterization).** For a positive-gain effect and a named spectrum, write $b,d$ for the spectrum's bright and dark rates and $\gamma=b-d>0$ for the spectral gap: a pulse is realizable if and only if two source-internal squared inequalities hold,
> $$(u^2+z^2)(b+d)^2\le(1-\mu)^2\gamma^2,\qquad (u^2+z^2)\bigl(2-b-d\bigr)^2\le(1+\mu)^2\gamma^2,\tag{S9.7}$$
> equivalently if and only if the generated background rate and rate factor form lawful rates; when realizable, the atomic effect built from that spectrum and the generated axis, after the detector, equals the original effect coordinatewise (background rate $<1$, efficiency $\in(0,1]$); two different feasible spectra can realize the same effect with different atoms. This is an "if and only if" characterization of realizability and does not concern semigroup existence.
>
> *Proof sketch.* Realizability is by definition the two remainder inequalities of background and detector; substituting the rate factor $g/\gamma$ and multiplying by $\gamma$, the two remainders match exactly the two squared inequalities of (S9.7) (both sides nonnegative, so squaring is an equivalence); the realized effect expands coordinatewise back to the original $(\mu,u,z)$; the spectrum can be recovered from the effect's maximal/minimal atomic readouts, so different spectra are distinguished at the atomic level. ∎

> **Proposition S9.4d (Area cap).** Under lawful detector rates ($\mathrm{Rates}\,d\,k$), a realization relation $\mathrm{Realizes}$, background $d<1$, bias bound $|\mu|\le B$, efficiency upper bound $0\le\eta_{\rm up}\le1$ with $\eta\le\eta_{\rm up}$, squared-area bound $0\le A_{\rm up}$ with $\mathcal A^2\le A_{\rm up}$, and the **forward inequality** $p^{\rm at}_{\max}\le7\mathcal A^2/4$ all holding,
> $$g\ \le\ \min\Bigl(1,\ \frac{(1+B)\,\eta_{\rm up}\,\bar a}{2-\eta_{\rm up}\,\bar a}\Bigr),\qquad \bar a=\min\Bigl(1,\frac{7A_{\rm up}}4\Bigr),\tag{S9.8}$$
> where $\mathcal A=\int\Omega_{12}\,dt$ is the dimensionless readout Rabi area and $p^{\rm at}_{\max}=(1+\mu_{\rm at}+g_{\rm at})/2$ the atomic effect's maximal click probability. The forward inequality itself is a conclusion of the numerical forward (next paragraph), not an internal conclusion of this theorem's premises; the theorem gives the gain bound given that forward inequality.
>
> *Proof sketch.* Atomic-readout upper bound: $p^{\rm at}_{\max}\le\min(1,7A_{\rm up}/4)=\bar a$ (composing the atomic gain $\le1$ with the forward inequality and the area bound); hence the efficiency×atomic product $\eta\cdot p^{\rm at}_{\max}\le\eta_{\rm up}\bar a\le1$; substituting into the product-cap theorem (raw_product_cap_gain: when $\eta\cdot p^{\rm at}_{\max}\le c\le1$, $g\le\min(1,(1+B)c/(2-c))$) gives (S9.8). ∎

*Dual-implementation numerical forward.* The GKSL forward of Garthoff's original 12-state matrix, 18 natural transitions and 7 ionization channels [12] is simulated separately by two programs sharing no forward computation, giving: (i) the forward inequality $\mathrm{gain}\le\min(1,7\mathcal A^2/4)$ consumed by Proposition S9.4d (the fixed-chart model's `source_inequality`, primary and independent receipts agreeing); (ii) strict lower bounds on each run and side's maximal readout Rabi area and its square (e.g. the 2016-04-15 uniform ray $\mathcal A^2>46056427315/120259084288$, $\mathrm{gain}>46056427315/68719476736$); (iii) the four named pulses realizable on all 32 domains of two runs × four roles, with six strictly different atomic responses still giving the same joint probabilities and every prefix factor (per-domain receipts). Note that the receipts also register `atomic_response_forward_model_kernel_proved=false`: the 12-state forward model itself is a dual-implementation numerical check, not a kernel theorem—this is exactly why the two evidence classes of this item are stated separately.

**(5) Complete history and post-measurement clock (mathematics plus dual-implementation check).**

> **Proposition S9.4d.** The complete history of the original source, visit 10 and run steps 16→17 keeps the current, the successor and every installed output; every step of the complete history fibre is uniquely determined by the complete observation; the original writer, whole ledger and installed projections are recovered item by item, the current field and the next field are both the original configuration, and the tick restrictions are retained.
>
> *Proof sketch.* Induction step by step: each step's complete observation uniquely determines that step's state and successor; the original record's fields are generated one by one by the writer's definition; the original-configuration identities of the current/next fields and the tick restrictions are per-projection identities. ∎

Two independent parsers recover the nine original fields of 41,673 local records and the 867 unpaired records (dual-implementation check, byte-level parse receipts); the original record clock additionally registers 41,603 positive intervals, 66 zero intervals and 4 right-censored ends, and the ordered two-clock commitment keeps the same history.

**Direct use.** The inverse image and fibre of (2)(3) are the carrier of §9.3's exact scale equivalence; (4)(5) connect the readout to the atomic hardware and the original history, cited by the boundary sentences of §9.2–9.3.

**Formal correspondence.** `Bell/ReadoutAnchors.lean` (`BlochProbe.{response,probability}`, probability nonnegativity and normalization, `recoveredU`, `recoveredZ`, `same_law_two_probes_unique`, `anchored_same_occurrence`, `same_law_split_probes_unique`), `Bell/ReadoutDetectorFiber.lean` (`click_bounds`, `click_gap`, `max_atomic_bounds`, `feasible_iff_rates`), `Bell/ReadoutPulseRealization.lean` (`realizationRates`, `realization_background_lt_one`, `realization_efficiency`, `pulse_realizes`, `feasible_gap_lower`, `realized_effect_eq`, `atomic_effect_injective`, `two_spectra_same_effect`), `Bell/SourceHistory.lean` (`next_generator`, `whole_history_read`, `history_frontier`, `whole_common_read`, `full_observation_event`, `constructor_code_faithful`, `complete_history_fibre`, `full_observation_determines_step`, `complete_model_determines_step`, `original_{writer,whole_ledger,installed_projection,entry,successor_entry}`, `current_field_is_original_configuration`, `next_field_is_original_configuration`, `original_{tick,next_tick}_restriction`); `munich/readout-domain/` receipts (`shared-response-verification.json`, `fiber-verification.json`, `pulse-realization-verification.json`, `atomic-forward-verification.json`, `detector-fiber-verification.json`, `history-verification.json`, `clock-verification-cl0001.json`). Commits AE (Lean and Munich consumers), AD (`Bell/TheoryBlind.lean`, `Readout{Effects,Identification,ResponseBounds}.lean`).

---

## S10 Table of first-release claims and proof locations

The selection indices agree with the `phys.Pn` of the first-release map of the public code selection (H0mework `docs/first-release-map.json`), for item-by-item review. The written proofs of P1–P22 are in the corresponding sections and appendices of the main text (locations per the selection's `text_location`); the written proofs of P24–P36 are in this supplement and the main text's proof ideas, with receipt identities in Appendix D.8.

| Selection index | Main-text result | Written proof | Pinned commit |
| --- | --- | --- | --- |
| phys.P1 | The master chain actually generated (Construction 4.1; Theorem 8.3) | §4, §8; Appendix C.8 | H |
| phys.P2 | The complete classical world and uniqueness (Theorems 4.2–4.4) | §4; Appendices A, B | H |
| phys.P3 | Early matter returned to the actual field (Proposition 2.5) | §2.5; Appendix A.3 | H |
| phys.P4 | The classical–quantum pairing identity (Theorem 6.2) | §6.1–6.2, eqs. (6.1)–(6.2) | H |
| phys.P5 | Current, kinetic loads, transport and exterior-power remainder (Theorem 6.3, Proposition 6.4) | §6.3–6.4; Appendix B.4 | H |
| phys.P6 | Complete representation, all events and macro successors (Theorem 8.3) | §8; Appendix C.8 | H |
| phys.P7 | All-real-time gauge–Dirac orbit (Theorem 7.1) | §7.1–7.2 | H |
| phys.P8 | Analytic predictions and the Bell probability family (Theorem 7.3, Proposition 7.4) | §7.3–7.4, §9.2; Appendix D.4 | H |
| phys.P9 | Formation of every physical source family (Theorem 8.1) | §8; Appendix C.2 | H |
| phys.P10 | Complete classical–quantum realization of every source (Theorem 8.1) | §8; Appendix C.8 | H |
| phys.P11 | Complete source path and autonomous programs (Theorem 8.2) | §8; Appendix C.3 | H |
| phys.P12 | Quantum time derivatives recover the orbit energy (Theorem 7.2) | §7.2 | H |
| phys.P13 | Generated geometry enters the actual action (Propositions 2.3–2.4, 3.3) | §2.3–2.4, §3.3; Appendices B.3, B.6 | H |
| phys.P14 | Exact signed elimination of the auxiliary fields (Theorem 3.2) | §3.2; Appendix B.2 | H |
| phys.P15 | Clock–B coupling and nonzero feedback (Construction 5.1, Theorems 5.2–5.4) | §5.1–5.4 | H |
| phys.P16 | Standard Fock preservation (Theorem 6.5, Example 6.6) | §6.5–6.6; Appendix D.3 | H |
| phys.P17 | Complete matter action formed from the mother material (Theorem C.1) | Appendix C.5 | H |
| phys.P18 | Complete joint carrier and nonzero feedback (Proposition C.2) | Appendix C.6 | H |
| phys.P19 | All-history all-order compact-domain bounds (Theorem 4.5) | §4 | H |
| phys.P20 | Mother-law completion and continuous-process representation (Proposition C.3) | Appendix C.7 | H |
| phys.P22 | Fixed mother source completely realized (Theorem 8.4, Corollary 8.5) | §8; Appendix C.9 | F |
| phys.P24 | The NIST 2015 nominal replay r0003 (§9.2; Appendix D.4.6) | S9.2(b); Appendix D.4.6 receipts | AB |
| phys.P25 | Conditional source member on public counts (Table S-II, §9.2) | S9.2(c) | AB |
| phys.P26 | Theorems 6.7–6.10 and the end of §6.9 (the complete quantum construction) | S1–S4, end of S3; §6.7–§6.10 | AB (the carrier of 6.7(1)(2) additionally at the four earlier commits `85cb5386…`, `f9b73392…`, `6726f385…`, `eec031c4…`, see S1) |
| phys.P27 | Theorem 6.12(1): the original complete 289 Green enters genuine finite-window field feedback | S6(1); §6.12 | AC (the feedback field operator and half-axis version at AE) |
| phys.P28 | The §9.2 observation-generated source slice and the same-source receiver update | S9.2(d) | AC |
| phys.P29 | Theorem 6.11: the mother action recovers the same $H_{289}$ | S5; §6.11 | AD |
| phys.P30 | Theorem 6.12(2)–(4): the complete-time paid half-axis, spectral axis and genuinely varying background | S6(2)–(4); §6.12 | AD ((2)'s half-axis consuming files and the exponential tail partly at AE) |
| phys.P31 | Proposition 9.1: the complete optical source domain and the joint 95% strictly positive CH | S9.1; §9.2 | AD |
| phys.P32 | Proposition 9.2(1)(2)(4)(5): prediction lock, readout domain, same-law scale, response bounds | S9.3; §7.4, §9.2 | AD |
| phys.P33 | Theorem 6.12(5): real-current operator and source-generated two-sided inverses + Theorem 6.13(3)–(5): static residue, constraint compatibility, origin weight | S6(5), S7(3)–(5); §6.12–6.13 | AE (static principal block, pole decomposition, Ward main line); the compatibility criterion, contact–deviation decomposition and price of 6.13(4)(5) at CAP |
| phys.P34 | Theorem 6.14: the matched original $\Gamma$ word's whole-frequency budget and the endpoint common tail | S8; §6.14 | AE |
| phys.P35 | Proposition 9.2(3) and Proposition 9.3: hardware inverse, pulse-realizable image, original post-measurement history | S9.3(3), S9.4; §9.2 | AE (Lean entries and Munich consumers) |
| phys.P36 | Theorem 6.13(1)–(3): the same-source moving carrier, momentum continuity and the varying-forcing field pole | S7(1)–(3); §6.13 | CAP (the base files of the static decomposition and (S7.3) are byte-identical in AE and CAP) |

The path prefixes in the "formal correspondence" rows: `alpha-source/` means `Verification/physics/low-energy-phenomenology/alpha-source/`, `external-composite-decay/` means `Verification/physics/low-energy-phenomenology/external-composite-decay/`, `Bell/` means `Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/`, `nist-real/` means `Verification/physics/stage10/independent-bell/nist-real/`, `munich/` means `Verification/physics/stage10/independent-bell/munich/`. The commit aliases and blob records are in `checks/first-release-source-audit.json`.
