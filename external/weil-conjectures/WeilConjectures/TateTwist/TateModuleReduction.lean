/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsCokernelPow
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.IntegersModPow
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientLinear
public import WeilConjectures.SixFunctors.ProEtale.SeparableClosureCover
public import WeilConjectures.TateTwist.TateModuleTrivialization

/-!
# The reduction of the Tate module modulo `ℓⁿ`

Let `X` be a scheme over a field `k` in which the prime `ℓ` is invertible, and let
`a : ℤ_ℓ ⟶ Λ` be a morphism of commutative condensed rings with `ℓⁿ = 0` in `Λ`. Then the
projection `ℤ_ℓ(1) ⟶ ℤ_ℓ,X ⊗ μ_{ℓⁿ}` from the Tate module becomes an isomorphism after extension
of scalars to `Λ_X` (`AlgebraicGeometry.ProEtale.isIso_extendScalars_map_tateModule_π`), so that
`Λ_X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1) ≅ Λ_X ⊗ μ_{ℓⁿ}` (`AlgebraicGeometry.ProEtale.extendScalarsTateModuleIso`).

This is checked on the pro-étale cover `X ×_k Spec kˢᵉᵖ ⟶ X`
(`ProEtale.CondensedRing.isIso_of_isIso_upperStar_map_of_cover`). Over a base `U` with a
compatible system of primitive `ℓⁿ`-th roots of unity, the pullback of the projection is, up to
isomorphisms, the reduction `S ⟶ S ⊗ 𝟙/ℓⁿ` of the regular module `S = g^* ℤ_ℓ,X`
(`ProEtale.upperStarTateModuleSystemIso`, `Mod.isLimitFreeCokernelPowTowerCone`), a cokernel of
`ℓⁿ`; extension of scalars to `Λ_U`, which is killed by `ℓⁿ`, sends it to an isomorphism
(`Mod.isIso_map_freeCokernelPowTowerCone_π`).

The hypothesis `ℓⁿ = 0` in `Λ` holds for the condensed rings `T̲` of a topological ring `T` in
which `ℓⁿ = 0` (`Profinite.natCast_zsmul_id_continuousMapRingObj_eq_zero`), e.g. for
`(𝒪_E ⧸ ℓⁿ)̲` (`Profinite.natCast_pow_zsmul_id_integersModPowRingObj_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

open scoped CategoryTheory.Obj

namespace Profinite

/-- If `m = 0` in the topological ring `T`, then `m = 0` in the condensed ring `T̲`. -/
lemma natCast_zsmul_id_continuousMapRingObj_eq_zero {T : Type} [TopologicalSpace T] [Ring T]
    [IsTopologicalRing T] {m : ℕ} (hm : (m : T) = 0) :
    ((m : ℕ) : ℤ) • 𝟙 (continuousMapRingObj.{u} T) = 0 := by
  ext S a
  have hd : ∀ b : ULift.{u + 1} C(S.unop, T), (m • b).down = m • b.down := fun _ ↦ rfl
  have h : (((m : ℕ) : ℤ) • 𝟙 (continuousMapRingObj.{u} T)).hom.app S = ((m : ℕ) : ℤ) • 𝟙 _ :=
    ((sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_zsmul (f := 𝟙 _) (r := ((m : ℕ) : ℤ))).trans (by simp)
  rw [h]
  refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
  simp [hd, nsmul_eq_mul, hm]

/-- `ℓⁿ = 0` in the condensed ring `(𝒪_E ⧸ ℓⁿ)̲`. -/
lemma natCast_pow_zsmul_id_integersModPowRingObj_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] (n : ℕ) :
    ((ℓ ^ n : ℕ) : ℤ) • 𝟙 (integersModPowRingObj.{u} ℓ E n) = 0 :=
  natCast_zsmul_id_continuousMapRingObj_eq_zero (by
    rw [Nat.cast_pow]
    exact PadicAlgCl.natCast_pow_eq_zero_integersModPow ℓ E n)

end Profinite

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

section Trivialized

variable {X U : Scheme.{u}} (g : U ⟶ X) [WeaklyEtale g] {K : Type u} [Field K]
  (f : U ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] {ζ : ℕ → K}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

/-- Over a base with a compatible system of primitive `ℓⁿ`-th roots of unity, the pullback of the
projection `ℤ_ℓ(1) ⟶ ℤ_ℓ,X ⊗ μ_{ℓⁿ}` is, up to isomorphisms, the reduction `S ⟶ S ⊗ 𝟙/ℓⁿ` of the
regular module `S = g^* ℤ_ℓ,X`. -/
lemma upperStar_map_tateModule_π_eq (n : ℕ) :
    ((g)^*[Ab.{u + 1}].mapMod _).map (limit.π (tateModuleSystem X ℓ) (op n)) =
      (IsLimit.conePointsIsoOfNatIso (isLimitOfPreserves ((g)^*[Ab.{u + 1}].mapMod _)
        (limit.isLimit (tateModuleSystem X ℓ)))
        (Mod.isLimitFreeCokernelPowTowerCone ((g)^*[Ab.{u + 1}].obj
          (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X)) ℓ
          (isLimitCokernelPowTowerConeOfIso
          (B := (g)^*[Ab.{u + 1}].obj
            (condensedRingObj (Profinite.continuousMapRingObj ℤ_[ℓ]) X))
          ((upperStarFromPointComp g).app (Profinite.continuousMapRingObj ℤ_[ℓ])).symm
          (isLimitCokernelPowTowerCone ℓ U)))
        (upperStarTateModuleSystemIso g f ℓ hζ hζ')).hom ≫
        (Mod.freeCokernelPowTowerCone _ ℓ).π.app (op n) ≫
          (upperStarTateModuleSystemIso g f ℓ hζ hζ').inv.app (op n) := by
  rw [← Category.assoc, IsLimit.conePointsIsoOfNatIso_hom_comp, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]
  rfl

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  (a : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom a] (n : ℕ)
  (hΛ : ((ℓ ^ n : ℕ) : ℤ) • 𝟙 Λ = 0)

omit [Fact ℓ.Prime] [MonObj Λ] [IsCommMonObj Λ] in
include hΛ in
/-- If `ℓⁿ = 0` in `Λ`, then `ℓⁿ = 0` in `Λ_X`. -/
lemma natCast_pow_zsmul_id_condensedRingObj_eq_zero (Y : Scheme.{u}) :
    ((ℓ ^ n : ℕ) : ℤ) • 𝟙 (condensedRingObj Λ Y) = 0 := by
  have := upperStarFromPoint_additive Y
  rw [← (upperStarFromPoint Y).map_id, ← Functor.map_zsmul, hΛ, Functor.map_zero]

include f hζ hζ' hΛ in
/-- Over a base with a compatible system of primitive `ℓⁿ`-th roots of unity, the pullback of the
extension of scalars of the projection `ℤ_ℓ(1) ⟶ ℤ_ℓ,X ⊗ μ_{ℓⁿ}` to a ring `Λ` killed by `ℓⁿ` is
an isomorphism. -/
theorem isIso_upperStar_map_extendScalars_map_tateModule_π :
    IsIso ((g)^*⟦Λ⟧.map ((Mod.extendScalars (coefficientMap a X)).map
      (limit.π (tateModuleSystem X ℓ) (op n)))) := by
  rw [← Functor.comp_map, ← NatIso.isIso_map_iff (pullIso a g), Functor.comp_map]
  let F := Mod.extendScalars (condensedPullbackHom (Profinite.continuousMapRingObj ℤ_[ℓ]) g) ⋙
    Mod.extendScalars (coefficientMap a U)
  have hF : IsIso (F.map ((Mod.freeCokernelPowTowerCone _ ℓ).π.app (op n))) :=
    Mod.isIso_map_freeCokernelPowTowerCone_π _ F ℓ n
      (Mod.zsmul_id_eq_zero_of_zsmul_id_eq_zero
        (natCast_pow_zsmul_id_condensedRingObj_eq_zero ℓ n hΛ U) _)
  have : IsIso (F.map (((g)^*[Ab.{u + 1}].mapMod _).map
      (limit.π (tateModuleSystem X ℓ) (op n)))) := by
    rw [upperStar_map_tateModule_π_eq g f ℓ hζ hζ' n, F.map_comp, F.map_comp]
    infer_instance
  exact this

end Trivialized

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (ℓ : ℕ) [Fact ℓ.Prime]
  [NeZero (ℓ : k)] {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]
  [IsCommMonObj Λ] (a : Profinite.continuousMapRingObj.{u} ℤ_[ℓ] ⟶ Λ) [IsMonHom a] (n : ℕ)
  (hΛ : ((ℓ ^ n : ℕ) : ℤ) • 𝟙 Λ = 0)

include f hΛ in
/-- **The reduction of the Tate module modulo `ℓⁿ`**: for a scheme `X` over a field in which `ℓ`
is invertible and a condensed ring `Λ` over `ℤ_ℓ` killed by `ℓⁿ`, the projection
`ℤ_ℓ(1) ⟶ ℤ_ℓ,X ⊗ μ_{ℓⁿ}` becomes an isomorphism after extension of scalars to `Λ_X`. -/
theorem isIso_extendScalars_map_tateModule_π :
    IsIso ((Mod.extendScalars (coefficientMap a X)).map
      (limit.π (tateModuleSystem X ℓ) (op n))) := by
  have : NeZero (ℓ : SeparableClosure k) :=
    ‹NeZero (ℓ : k)›.of_injective (algebraMap k (SeparableClosure k)).injective
  obtain ⟨ζ, hζ, hζ'⟩ := IsSepClosed.exists_isPrimitiveRoot_pow_eq (SeparableClosure k) ℓ
  refine isIso_of_isIso_upperStar_map_of_cover Λ _ (sepClosureCover f) fun i ↦ ?_
  have : WeaklyEtale ((sepClosureCover f).f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ (sepClosureCover f).mem₀ (.mk i)
  have p : (sepClosureCover f).X i ⟶ Spec (.of (SeparableClosure k)) :=
    pullback.snd f (specSepClosureHom k)
  exact isIso_upperStar_map_extendScalars_map_tateModule_π ((sepClosureCover f).f i) p ℓ hζ hζ'
    a n hΛ

/-- **The reduction of the Tate module modulo `ℓⁿ` is `μ_{ℓⁿ}`**: for a scheme `X` over a field
in which `ℓ` is invertible and a condensed ring `Λ` over `ℤ_ℓ` killed by `ℓⁿ`,
`Λ_X ⊗_{ℤ_ℓ,X} ℤ_ℓ(1) ≅ Λ_X ⊗ μ_{ℓⁿ}`. -/
noncomputable def extendScalarsTateModuleIso :
    (Mod.extendScalars (coefficientMap a X)).obj (tateModule X ℓ) ≅
      (Mod.freeFunctor (condensedRingObj Λ X)).obj (rootsOfUnitySheaf X (ℓ ^ n)) :=
  have := isIso_extendScalars_map_tateModule_π f ℓ a n hΛ
  asIso ((Mod.extendScalars (coefficientMap a X)).map (limit.π (tateModuleSystem X ℓ) (op n))) ≪≫
    (Mod.freeFunctorCompExtendScalarsIso (coefficientMap a X)).app (rootsOfUnitySheaf X (ℓ ^ n))

end AlgebraicGeometry.ProEtale
