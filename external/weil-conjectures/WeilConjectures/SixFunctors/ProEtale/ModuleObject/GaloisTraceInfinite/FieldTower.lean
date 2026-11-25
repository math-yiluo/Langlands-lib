/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.SheafColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.GaloisLevel
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.ModuleObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginComplex
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.SubfieldLinear

/-!
# The Galois tower of a Galois extension of fields

Let `Ω/L` be a Galois extension (possibly infinite) and `h : G ⟶ Spec L`. The finite Galois
subextensions `L'` give the Galois tower `G ×_L L' ⟶ G` with limit `G ×_L Ω`
(`AlgebraicGeometry.ProEtale.galoisTower`).

For a finite discrete commutative ring `T` in which the degrees `[L' : L]` are invertible (for
instance `𝒪_E/ϖⁿ` and `Ω/L` pro-`p` with `p ≠ ℓ`) and `Λ = C(-, T)`, every object `C` of
`D(Mod_{Λ_G})` which is bounded below of étale origin has a retraction of the derived unit
`C ⟶ Rg_* Lg^* C`, `g : G ×_L Ω ⟶ G`, invariant under the derived unit transports along the
automorphisms `Spec σ`, `σ ∈ Gal(Ω/L)`
(`AlgebraicGeometry.ProEtale.exists_invariant_retraction_derivedUnit_galois`): this is the
`Gal(Ω/L)`-invariant part of `Rg_* Lg^* C`, the derived form of Hochschild–Serre for a pro-`p`
group with coefficients in which `p` is invertible.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [IsGalois L Ω] {G : Scheme.{u}}
  (h : G ⟶ Spec (.of L))

instance weaklyEtale_specMap_algebraMap_of_isSeparable (K K' : Type u) [Field K] [Field K']
    [Algebra K K'] [Algebra.IsSeparable K K'] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap K K'))) := by
  have := Algebra.IndEtale.of_isSeparable K K'
  exact inferInstanceAs (WeaklyEtale (specFieldMap K K'))

variable (Ω) in
/-- **The Galois tower of a Galois extension** `Ω/L` over `h : G ⟶ Spec L`: the finite levels
`G ×_L L'` for the finite Galois subextensions `L'`, with Galois groups `Gal(L'/L)`, and the limit
`G ×_L Ω`. -/
noncomputable def galoisTower :
    GaloisTower (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))) where
  J := FiniteGaloisIntermediateField L Ω
  Y L' := pullback h (Spec.map (CommRingCat.ofHom (algebraMap L L')))
  g L' := pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L L')))
  weaklyEtale _ := inferInstance
  surjective _ := inferInstance
  quasiCompact _ := inferInstance
  t hle := galoisLevelMap Ω h hle
  t_g hle := galoisLevelMap_fst h hle
  t_refl _ := galoisLevelMap_refl h _
  t_comp h₁ h₂ := galoisLevelMap_comp h h₁ h₂ _
  π L' := galoisLevelProjection h L'
  π_g L' := galoisLevelProjection_fst h L'
  π_t hle := galoisLevelProjection_comp_galoisLevelMap h hle
  Γ L' := L' ≃ₐ[L] L'
  ρ L' := galoisLevelAction h L'
  ρ_g L' := pullbackAction_fst h _ (specGaloisAction_comp (F := L) (L := L'))
  ρ_mul L' := pullbackAction_mul h _ _ (specGaloisAction_mul (F := L) (L := L'))
  isGaloisAction _ := IsGaloisAction.pullback h _ _ isGaloisAction_spec
  exists_lift hle σ := exists_galoisLevelMap_comp_galoisLevelAction h hle σ

namespace CondensedRing

/-- **Invertibility of the degree on module objects**: if `n` is a unit in a ring `K` of constants
of `Λ`, multiplication by `n` is invertible on every `Λ_X`-module object. -/
lemma isIso_nsmul_id_mod_of_isUnit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {K : Type*} [CommRing K] (φ : K →+* CategoryTheory.MonObj.Γ Λ)
    {X : Scheme.{u}}
    {n : ℕ} (hn : IsUnit (n : K))
    (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsIso (n • 𝟙 N) := by
  let := modLinear Λ φ X
  obtain ⟨v, hv⟩ := hn
  have e : n • 𝟙 N = (v : K) • 𝟙 N := by rw [hv, Nat.cast_smul_eq_nsmul]
  rw [e]
  refine ⟨⟨(↑v⁻¹ : K) • 𝟙 N, ?_, ?_⟩⟩ <;>
    simp only [Linear.smul_comp, Linear.comp_smul, id_comp, smul_smul, Units.mul_inv,
      Units.inv_mul, one_smul]

end CondensedRing

/-- An étale-origin module object has an étale-origin underlying abelian sheaf. -/
lemma essImage_comparisonUpperStar_X {X : Scheme.{u}} (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X))
    (F₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T₀)))
    (e : (finiteCoefficientModEquivalence X T₀).functor.obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) X).obj F₀) :
    (comparisonUpperStar AddCommGrpCat.{u + 1} X).essImage M.X :=
  ⟨(sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) AddCommGrpCat.{u + 1})).obj F₀,
    ⟨(sheafComposeForget₂CompComparisonUpperStarIso _ X).app F₀ ≪≫
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) AddCommGrpCat.{u + 1})).mapIso e.symm⟩⟩

variable (Ω) in
/-- For a module object `M` of étale origin, `g_* g^* M` is the colimit of the finite levels of
the Galois tower. -/
noncomputable def isColimitModuleCocone_galoisTower (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) G))
    (hM : (comparisonUpperStar AddCommGrpCat.{u + 1} G).essImage M.X) :
    IsColimit ((galoisTower Ω h).moduleCocone (Profinite.continuousMapRingObj T₀) M) :=
  (galoisTower Ω h).isColimitModuleCocone _ _
    (nonempty_isColimit_galoisUpperLowerCocone (Ω := Ω) h M.X hM).some

/-- **Galois invariant retraction of the derived unit of an infinite Galois extension** (the
derived Hochschild–Serre isomorphism for a pro-`p` Galois group, with torsion coefficients in which
`p` is invertible). Let `Ω/L` be Galois, `h : G ⟶ Spec L`, `g : G ×_L Ω ⟶ G`, `T₀` a finite
discrete commutative ring in which the degrees of the finite Galois subextensions of `Ω/L` are
invertible, `Λ = C(-, T₀)`, and `C ∈ D(Mod_{Λ_G})` bounded below of étale origin. Then the derived
unit `C ⟶ Rg_* Lg^* C` has a retraction `R` fixed by the derived unit transports along all the
`Spec σ`, `σ ∈ Gal(Ω/L)`. -/
theorem exists_invariant_retraction_derivedUnit_galois (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (hp : ∀ L' : FiniteGaloisIntermediateField L Ω, IsUnit ((Module.finrank L L' : ℕ) : T₀))
    (C : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) G)))
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀)) G
      ((finiteCoefficientDerivedEquivalence G T₀).functor.obj C)) :
    ∃ R : R((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj T₀⟧).obj
          (L((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
            Profinite.continuousMapRingObj T₀⟧).obj C) ⟶ C,
      (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T₀)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).unit.app C ≫ R =
        𝟙 _ ∧
      ∀ σ : Ω ≃ₐ[L] Ω, derivedUnitTransport (Profinite.continuousMapRingObj T₀)
          (pullbackAction h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ)
          (pullbackAction_fst h _ specGaloisAction_comp σ) C ≫ R = R := by
  obtain ⟨K, a, hKa, hterms, ⟨e⟩⟩ := exists_complex_of_plusEtaleOrigin T₀ C hC
  choose F₀ hF₀ using hterms
  have hd : ∀ (j : FiniteGaloisIntermediateField L Ω)
      (N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T₀) G)),
      IsIso (Fintype.card ((galoisTower Ω h).Γ j) • 𝟙 N) := fun j N ↦ by
    have hc : Fintype.card ((galoisTower Ω h).Γ j) = Module.finrank L j := by
      change Fintype.card (j ≃ₐ[L] j) = _
      rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    rw [hc]
    exact CondensedRing.isIso_nsmul_id_mod_of_isUnit _ (Profinite.continuousMapConstRingHom T₀)
      (hp j) N
  have hc := fun n ↦ isColimitModuleCocone_galoisTower Ω h T₀ (K.X n)
    (essImage_comparisonUpperStar_X T₀ (K.X n) (F₀ n) (hF₀ n).some)
  have hK := fun n ↦
    rightAcyclic_condensedRingLowerStar_upperStar_of_iso (Ω := Ω) T₀ h (K.X n) (F₀ n) (hF₀ n)
  obtain ⟨R, hR₁, hR₂⟩ := (galoisTower Ω h).exists_invariant_retraction_derivedUnit_of_iso
    (Profinite.continuousMapRingObj T₀) hd K hc a hK C e
  exact ⟨R, hR₁, fun σ ↦ hR₂ _ _ fun (j : FiniteGaloisIntermediateField L Ω) ↦
    ⟨σ.restrictNormal j, pullbackAction_comp_galoisLevelProjection h j σ⟩⟩

end AlgebraicGeometry.ProEtale
