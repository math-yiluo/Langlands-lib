/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived

/-!
# Torsion sheaves with orders invertible in a field

For a field `K`, a sheaf of `Λ`-modules on the small étale site of a `K`-scheme has *orders
invertible in `K`* if every element of every geometric stalk is killed by a positive integer
`n` with `n ≠ 0` in `K`. In the repository this is
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder (Spec K)`, whose defining condition
asks for `n` to be a unit in `Γ(Spec K, ⊤) ≅ K`.

## Main statements

- `AlgebraicGeometry.Scheme.isTorsionSheafOfInvertibleOrder_spec_iff`
  (`corollary-open-direct-image-over-field--2`): the characterisation in terms of `K`.
- `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero`
  (`corollary-open-direct-image-over-field--2`): sheaves of modules over a ring killed by an integer
  invertible in `K` have orders invertible in `K`.
- `AlgebraicGeometry.Scheme.isTorsionSheafOfInvertibleOrder_iff_exists_isColimit`
  (`corollary-open-direct-image-over-field--2`): a sheaf has orders invertible on `S` if and only if
  it is a filtered colimit of sheaves killed by integers invertible on `S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- A natural number is a unit in `Γ(Spec K, ⊤)` if and only if it is nonzero in `K`. -/
lemma isUnit_natCast_Γ_spec_iff {K : Type u} [Field K] (n : ℕ) :
    IsUnit (n : Γ(Spec (.of K), ⊤)) ↔ (n : K) ≠ 0 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  rw [← isUnit_iff_ne_zero, ← MulEquiv.isUnit_map e.toMulEquiv]
  simp

/-- Blueprint `corollary-open-direct-image-over-field--2`: **orders invertible in a field.** For a
field `K`, a sheaf `F` of `Λ`-modules on the small étale site of a scheme `T` has orders invertible
in `K` (`IsTorsionSheafOfInvertibleOrder (Spec K) F`) if and only if every element of every
geometric stalk of `F` is killed by an integer `n ≥ 1` with `n · 1_K ≠ 0`. A complex has
torsion cohomology with orders invertible in `K` if all its cohomology sheaves have this
property. -/
theorem isTorsionSheafOfInvertibleOrder_spec_iff {K : Type u} [Field K] {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
        (x : ↥((pointSmallEtale s).sheafFiber.obj F)),
          ∃ n : ℕ, 0 < n ∧ (n : K) ≠ 0 ∧ n • x = 0 := by
  simp_rw [← isUnit_natCast_Γ_spec_iff]
  exact ⟨fun h ↦ h.exists_isUnit_nsmul_eq_zero, fun h ↦ ⟨h⟩⟩

/-- Blueprint `corollary-open-direct-image-over-field--2`: **modules over `ℤ/nℤ` have invertible
orders.** If an integer `n ≥ 1`, nonzero in the field `K`, kills the coefficient ring `Λ` (for
instance `Λ = ℤ/nℤ`), then every sheaf of `Λ`-modules on the small étale site of a scheme has
orders invertible in `K`: multiplication by `n` is zero on it. -/
theorem IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero_of_ne_zero {K : Type u} [Field K]
    {T : Scheme.{u}} (n : ℕ) (hn₀ : n ≠ 0) (hn : (n : Λ) = 0) (hnK : (n : K) ≠ 0)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F :=
  IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn₀ hn
    ((isUnit_natCast_Γ_spec_iff n).2 hnK) F

/-- Blueprint `corollary-open-direct-image-over-field--2`: **the colimit description of invertible
orders.** A sheaf `F` of `Λ`-modules on the small étale site of `T` has orders invertible on
`S` if and only if it is the colimit of a filtered diagram of sheaves each of which is killed by
a positive integer invertible on `S` (for `S = Spec K`, `F = colim_{n ∈ I_K} F[n]`).

One direction is `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder.exists_isColimit`.
Conversely, the geometric stalks commute with the colimit, the stalk functors being left
adjoints, so every element of a stalk of `F` comes from a stalk of some member of the diagram,
where it is killed by the corresponding integer. -/
theorem isTorsionSheafOfInvertibleOrder_iff_exists_isColimit (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsTorsionSheafOfInvertibleOrder S F ↔
      ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
        (D : J ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (c : Cocone D)
        (_ : IsColimit c), c.pt = F ∧
          ∀ j, ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • 𝟙 (D.obj j) = 0 := by
  refine ⟨fun _ ↦ IsTorsionSheafOfInvertibleOrder.exists_isColimit Λ S F, ?_⟩
  rintro ⟨J, _, _, D, c, hc, rfl, hD⟩
  refine ⟨fun Ω _ _ s x ↦ ?_⟩
  let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : Φ.Additive := (pointSmallEtale s).sheafFiber_additive
  have : PreservesColimitsOfShape J (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    have := preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
    inferInstance
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _ (isColimitOfPreserves Φ hc) x
  obtain ⟨n, hn, hnS, hDn⟩ := hD j
  refine ⟨n, hn, hnS, ?_⟩
  have h0 : Φ.map (n • 𝟙 (D.obj j)) y = 0 := by
    rw [hDn, Φ.map_zero]
    rfl
  rw [Φ.map_nsmul, Φ.map_id] at h0
  have h1 : n • y = 0 := by simpa using h0
  have h2 : ((Φ.mapCocone c).ι.app j) (n • y) = 0 := by
    rw [h1]
    exact map_zero _
  simpa using h2

end Scheme

end AlgebraicGeometry
