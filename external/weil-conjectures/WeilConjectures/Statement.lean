/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Weil.Definitions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.ZetaFunction.Rationality
public import WeilConjectures.ZetaFunction.SmoothProper

@[expose] public section

/-!
# The Weil conjectures

Let `X` be a smooth, proper, geometrically integral scheme of dimension `d` over a finite
field `k` with `q` elements and let `Z(X, t) ∈ ℚ⟦t⟧` be its zeta function
(`AlgebraicGeometry.Scheme.zetaSeries`). The Weil conjectures [weil1949] assert:

1. *Rationality* (Dwork, 1960): `Z(X, t)` is a rational function. More precisely
   `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` for polynomials `Pᵢ ∈ ℤ[t]` with
   `Pᵢ(0) = 1`, `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`, the odd-indexed ones in the
   numerator and the even-indexed ones in the denominator. Rationality alone holds for
   arbitrary schemes of finite type over `k`, see `zetaSeries_rational`.
2. *Functional equation* (Grothendieck, 1965): `Z(X, 1 / (qᵈ t)) = ± q^{dχ/2} tᵡ Z(X, t)`
   where `χ = ∑ (-1)ⁱ deg Pᵢ`. Equivalently — and this is how we state it — the map
   `α ↦ qᵈ / α` sends the inverse roots of `Pᵢ` bijectively (with multiplicity) to the
   inverse roots of `P_{2d - i}`.
3. *Riemann hypothesis* (Deligne, 1974): the inverse roots of `Pᵢ` are algebraic numbers
   of absolute value `q^{i/2}` under every complex embedding. Since each `Pᵢ` has integer
   coefficients and constant coefficient `1`, its inverse roots are automatically
   algebraic integers, so we only need to constrain the norms of its complex roots.

We state the three conjectures in terms of the complex roots of the `Pᵢ`: a root `z` of
`Pᵢ` is the inverse of an inverse root `α`, so the Riemann hypothesis reads
`‖z‖ = q^{-i/2}` and the functional equation says that `z ↦ 1 / (qᵈ z)` maps the root
multiset of `Pᵢ` to that of `P_{2d - i}`.

Weil's fourth conjecture — if `X` lifts to a smooth proper scheme over a number ring, then
`deg Pᵢ` is the `i`-th Betti number of the associated complex manifold — needs singular
cohomology of the analytification and is not stated here. In the Grothendieck-Deligne
proof `deg Pᵢ` is the `ℚ_ℓ`-dimension of the `i`-th étale cohomology of the base change of
`X` to an algebraic closure of `k`; compare `Scheme.EllAdicCohomology`.

The predicates `AlgebraicGeometry.IsWeilFactorization`,
`AlgebraicGeometry.WeilFunctionalEquation` and `AlgebraicGeometry.WeilRiemannHypothesis`
spelling out the three conjectures are defined in `Comparator/Weil/Definitions.lean`, since
they are needed to state the comparator challenge of this repository (see
`Comparator/README.md`).

## Main statements

- `AlgebraicGeometry.Scheme.zetaSeries_rational`: rationality of `Z(X, t)` for arbitrary
  `X` of finite type over `k` (Dwork's theorem).
- `AlgebraicGeometry.Scheme.weil_conjectures`: the Weil conjectures for a smooth, proper,
  geometrically integral scheme over a finite field.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
-/

universe u

open Polynomial

namespace AlgebraicGeometry

namespace Scheme

variable {k : Type u} [Field k] [Finite k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Dwork's theorem**: the zeta function of a scheme of finite type over a finite field
is a rational function with integer coefficients. This is the first Weil conjecture, which
holds without any smoothness or properness hypotheses. -/
theorem zetaSeries_rational [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  f.exists_int_mul_zetaSeries_eq

/-- **The Weil conjectures** (Dwork, Grothendieck, Deligne): the zeta function of a
smooth, proper, geometrically integral scheme `X` of dimension `d` over a finite field
`k` with `q` elements factors as `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` with
`Pᵢ ∈ ℤ[t]`, `Pᵢ(0) = 1`, `P₀ = 1 - t`, `P_{2d} = 1 - qᵈ t`, satisfying the functional
equation and the Riemann hypothesis: all inverse roots of `Pᵢ` have absolute value
`q^{i/2}`, and `α ↦ qᵈ / α` matches the inverse roots of `Pᵢ` with those of `P_{2d-i}`.
(blueprint: `theorem-weil-conjectures-smooth-proper-schemes`) -/
theorem weil_conjectures (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [GeometricallyIntegral f] :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k) d P ∧
      WeilRiemannHypothesis (Nat.card k) d P := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k)) :=
    ‹SmoothOfRelativeDimension d f›
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := ‹IsProper f›
  have : GeometricallyConnected (X ↘ Spec (CommRingCat.of k)) :=
    GeometricallyIntegral.geometricallyConnected f
  obtain ⟨P, h₁, h₂, h₃, -⟩ := exists_isWeilFactorization_of_smoothProper k X d
  exact ⟨P, h₁, h₂, h₃⟩

end Scheme

end AlgebraicGeometry
