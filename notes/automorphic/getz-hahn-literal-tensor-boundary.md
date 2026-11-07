# Getz–Hahn (6.1): the literal algebraic tensor removes cusp forms

Worker 116 wrote this note on 7 November 2026 against Library commit
`568f1cff4df2c51ba08b932716bf99235d0032c7`, for standing program
`34b81620-20d7-4059-9b08-6bedd1c1c029`. It is a mathematical argument about
a source convention. It is not an accepted Lean result.

The note shows that the literal reading of Getz–Hahn (6.1) is too
restrictive for non-compactly supported functions. Read literally, every
left `G(F)`-invariant smooth function is invariant under the adelic points
of each rational unipotent radical. So if `G` has a proper rational
parabolic, the only literal cusp form is zero. For `GL_n` with `n ≥ 2`, every
such function factors through the determinant. The compactly supported
line of (6.1) is not affected. The correct convention for automorphic
forms is the one of Borel–Jacquet §4.1, which the Library's broader form
carriers already implement. The planned comparison between the literal
tensor spaces and those carriers is therefore false, and should not be
attempted.

## Sources

- Getz–Hahn, *An Introduction to Automorphic Representations*, GTM 300
  (2024), registered as `getz-hahn-2024-automorphic-representations`,
  file SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
  Page numbers below are printed pages, with one-based PDF pages in
  brackets.
  - (6.1), printed p.158 [PDF 172]: `C^∞(G(A_F)) := C^∞(G(F_∞)) ⊗
    C^∞(G(A_F^∞))`, the same for `C_c^∞` and for `A_G \ G`. The text says
    "Here the tensor products are algebraic."
  - Definition 5.2.1, printed p.136 [PDF 151]: the finite factor
    `C^∞(G(A_F^∞))` consists of the locally constant functions.
  - Definition 6.3.1, printed pp.161–162 [PDF 175–176]: "Any smooth `φ`
    can be written as a finite sum of vectors of the form `φ_∞ ⊗ φ^∞`",
    which is used to define `Xφ` for `X ∈ U(g)`.
  - Definition 6.3.3, printed p.163 [PDF 177]: an automorphic form is a
    smooth function of moderate growth that is left `G(F)`-invariant,
    `K`-finite and `Z(g)`-finite.
  - Definition 6.5.1 and (6.18), printed p.167 [PDF 181]: cusp forms are
    the automorphic forms whose constant terms along all proper parabolics
    vanish.
- Getz–Hahn errata, October 2026 author version, registered as
  `getz-hahn-2024-errata-2026-10`, SHA-256
  `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
  All five pages were searched; no entry concerns (6.1), Definition 6.3.1
  or the finite-sum statement.
- Borel–Jacquet, Corvallis 1979 Part I, registered as
  `borel-jacquet-1979-automorphic`, SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
  §4.1, printed p.194 (one-based PDF p.189): a function on `G(A)` is
  smooth if it is continuous, `C^∞` in the archimedean variable and
  locally constant in the finite variable. §4.2(b), printed p.195, adds
  `f * ξ = f` for a simple Hecke element. This gives right invariance under
  one compact open subgroup.

## The degeneration statement

Let `F` be a number field, `G` a connected reductive group over `F`, and
write `G(A_F) = G(F_∞) × G(A_F^∞)`. Call `φ : G(A_F) → ℂ` *literally
smooth* if there are finitely many smooth `a_p` on `G(F_∞)` and locally
constant `b_p` on `G(A_F^∞)` with `φ(x, y) = Σ_p a_p(x) b_p(y)` everywhere.
Such a `φ` is continuous. No growth, `K`-finiteness or `Z(g)`-finiteness
is used below.

**Claim.** Let `φ` be literally smooth and left `G(F)`-invariant. Let `P`
be a proper parabolic `F`-subgroup with unipotent radical `N`.

1. For every `x ∈ G(A_F)`, the function `n ↦ φ(n x)` is constant on
   `N(A_F)`. So the constant term of `φ` along `P`, for the mass-one measure
   on `N(F) \ N(A_F)`, equals `φ`.
2. If `φ` is cuspidal along `P`, then `φ = 0`. In particular the literal
   cusp-form space of `G` is zero as soon as `G` has a proper parabolic
   `F`-subgroup.
3. For `G = GL_n` with `n ≥ 2`, there is a function `ψ` on `F^× \ A_F^×`
   with `φ(g) = ψ(det g)` for all `g`.

### Proof

For `y ∈ G(A_F^∞)` write `φ_y(x) = φ(x, y)`, a function on `G(F_∞)`.

*Step 1: slices lie in one finite-dimensional space.* Every `φ_y` lies in
`W = span{a_p}`, so `dim W` is at most the number of terms.

*Step 2: rational translation moves slices.* For `γ ∈ G(F)`, left
invariance applied to `(γ^{-1} x, y)` gives
`φ_{γ y}(x) = φ_y(γ^{-1} x)`. So the `G(F)`-span of `φ_y` under left
translation lies in `W`.

*Step 3: each slice has a congruence stabilizer.* Fix `y`. The finitely
many `b_p` are constant on a neighbourhood of `y`, hence on `y L` for a
compact open subgroup `L` of `G(A_F^∞)`. So `φ_{y'} = φ_y` for every
`y' ∈ y L`. If `γ ∈ Γ_y := G(F) ∩ y L y^{-1}`, then `γ y ∈ y L` and
Step 2 gives `φ_y(γ^{-1} x) = φ_{γ y}(x) = φ_y(x)`. Thus `φ_y` is left invariant under
the congruence subgroup `Γ_y`.

*Step 4: the stabilizer is normal-closed.* The `G(F)`-span `W_y` of `φ_y`
has a basis `φ_{c_1}, …, φ_{c_m}` with `c_i ∈ G(F) y`. Choose `L_i` for
`c_i` as in Step 3. The common stabilizer of the basis contains
`Γ' = G(F) ∩ L'` with `L' = ⋂_i c_i L_i c_i^{-1}`, again a compact open
subgroup. So every element of `W_y` is `Γ'`-invariant. Applying this to
`φ_{γ y}` and using Step 2, `φ_y` is invariant under `γ^{-1} Γ' γ` for all
`γ ∈ G(F)`. So `φ_y` is invariant under the normal closure `Γ'^{G(F)}`.

*Step 5: the normal closure contains `N(F)`.* Every parabolic
`F`-subgroup of a connected reductive group is the dynamic subgroup `P(λ)`
of an `F`-cocharacter `λ`. In the Library this is the proposition
`Langlands.GroupScheme.ParabolicDynamicStatement`, whose docstring cites
Milne, Theorem 25.1. It has no Lean proof yet.
Choose such a `λ`, so that `Ad λ(s)` acts on `Lie N` with weights
`k ≥ 1`. The exponential identifies `Lie N (F)` with `N(F)`. Since
`Γ' ∩ N(F) = N(F) ∩ L'` with `L'` open, `Γ' ∩ N(F)` contains `exp` of a
`ℤ`-lattice `Λ = ⊕_k Λ_k` with `Λ_k` a full lattice in the weight-`k` part.
Given `X = Σ_k X_k`, choose a positive integer `M` with `M X_k ∈ Λ_k` for all
`k`. Then `Y = Σ_k M^k X_k ∈ Λ` and `Ad λ(1/M) Y = X`. So
`exp X = λ(1/M) exp(Y) λ(1/M)^{-1}`, which lies in `Γ'^{G(F)}`.

*Step 6: archimedean invariance.* `N(F)` is dense in `N(F_∞)`, because
`F` is dense in `F_∞` and `exp` is a polynomial isomorphism from the Lie
algebra. Each `φ_y` is continuous, so it is left invariant under `N(F_∞)`.

*Step 7: constancy on `N(A_F)`.* Fix `x`. The continuous function
`f(n) = φ(n x)` on `N(A_F)` is invariant under left multiplication by
`N(F)` (automorphy) and by `N(F_∞) × {1}` (Step 6 applied to the slice
at the finite component of `n x`). `N(F)` is dense in `N(A_F^∞)`, since `F`
is dense in `A_F^∞`. So the products `(u, 1) γ` with `u ∈ N(F_∞)` and
`γ ∈ N(F)` are dense in `N(A_F)`. By continuity `f` is invariant under all
left translations, hence constant. This proves part 1. Part 2 follows because
the mass-one constant term is then `φ` itself.

*Step 8: `GL_n`.* Take `γ = diag(1, …, s, …, 1)` with `s` in position `i`.
Then `γ^{-1} e_{ij}(t) γ = e_{ij}(s^{-1} t)`, where `e_{ij}(t)` is the
elementary matrix. `Γ'` contains `e_{ij}(t)` for all `t` in a nonzero ideal
of `O_F`. Step 4 then gives invariance of each `φ_y` under every
`e_{ij}(u)` with `u ∈ F`. These matrices generate `SL_n(F)`, which is dense
in `SL_n(F_∞)`. So every slice is left `SL_n(F_∞)`-invariant. Hence `φ` is
left invariant under `SL_n(F_∞) × {1}` and under `GL_n(F)`. The closure of
the group these generate contains `SL_n(A_F)`, because `SL_n(F)` is dense in
`SL_n(A_F^∞)`. As `SL_n(A_F) \ GL_n(A_F) ≅ A_F^×` via `det`, part 3 follows. ∎

### Example

Let `G = SL_2` over `ℚ` and let `φ` be the adelic lift of the weight-12 cusp
form `Δ`, right invariant under `SL_2(Ẑ)`. Step 2 gives slices
`x ↦ φ_∞(γ^{-1} x)` for all `γ ∈ SL_2(ℚ)`. For `γ = diag(m^{-1}, m)` these
correspond to the classical forms `m^{12} Δ(m^2 z)`. Their `q`-expansions
start at `q^{m^2}`, so infinitely many slices are linearly independent. So
`φ` is not literally smooth, as Step 1 also shows.

## The compactly supported line is correct

Let `f` be continuous with compact support, smooth in the archimedean
variable, and right invariant under a compact open subgroup `L` of
`G(A_F^∞)`. Then the support meets finitely many cosets `c L`, and
`f = Σ_c f(·, c) ⊗ 1_{cL}` is a finite sum. So
`C_c^∞(G(F_∞)) ⊗ C_c^∞(G(A_F^∞))` is exactly the space of such functions.
The test functions in `R(f)` and Hecke operators can follow GH (6.1)
literally.

The right invariance under one `L` is needed. Slice-wise local constancy
alone does not give it: one can let the radius of constancy shrink to
zero as the archimedean variable tends to a point.

## Consequences for the Library

- `GroupSchemeForms`, `GroupSchemeCuspidalForms` and the `[G]` modules built
  on them use the finite plot-smooth carrier. It consists of continuous
  rational-invariant functions with smooth infinite slices and one common
  open finite stabilizer. This is the Borel–Jacquet §4.1–4.2 convention,
  and it is the carrier the spectral chain should use.
- `GroupSchemeTensorSmooth` (`adelicTensorSmoothFunctions`,
  `tensorSmoothSubrepresentation`, `finiteTensorSmoothSubrepresentation`),
  `GroupSchemeTensorForms` (`tensorAdelicAutomorphicSubrepresentation`),
  `GroupSchemeTensorCuspidalL2` and `GroupSchemeRestrictionTensorCuspidalL2`
  implement the literal tensor condition. Their Markdown correctly claims no
  equality with the broader carriers. By the claim above, for a group with a
  proper parabolic `F`-subgroup, their cusp spaces are mathematically zero.
  Step 5 uses the dynamic description of parabolics, which those cusp
  modules already carry as the explicit hypothesis
  `ParabolicDynamicStatement`. For `GL_n` with `n ≥ 2`, their automorphic
  spaces consist of determinant pullbacks. No Lean theorem states either
  fact yet.
- Several Library Markdown files and DAG descriptions list a "literal GH
  tensor comparison" as a remaining obligation. The inclusion of the literal
  spaces into the broader ones is already published. The converse
  inclusion is false for every group with a proper parabolic `F`-subgroup,
  so it should be dropped rather than assigned. A formal counterexample
  would be a separate, optional unit.
- Uniform moderate growth (GH Definition 6.3.1) can be defined slice-wise,
  as `X` acts only on the archimedean variable. The finite-sum statement
  printed there is not needed.
