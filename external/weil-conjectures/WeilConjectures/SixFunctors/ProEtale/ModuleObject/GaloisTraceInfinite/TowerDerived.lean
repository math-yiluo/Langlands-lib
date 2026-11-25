/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.ModuleObject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitTransportAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# The derived unit of a Galois tower is split by an invariant retraction

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) with Galois groups
of order invertible in `Λ`, and let `K` be a bounded below complex of `Λ_X`-module objects such
that, at every term, `g_{∞*} g_∞^* Kⁿ` is the colimit of the finite levels and `g_∞^* Kⁿ` is
`g_{∞*}`-acyclic. Then the unit `K ⟶ Rg_{∞*} Lg_∞^* K` of the derived adjunction has a retraction
`R`, induced by the levelwise normalized traces
(`AlgebraicGeometry.ProEtale.GaloisTower.complexTrace`), which is invariant under the derived unit
transports along the automorphisms of `Y_∞` over `X` compatible with the Galois actions
(`AlgebraicGeometry.ProEtale.GaloisTower.exists_invariant_retraction_derivedUnit`).
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Naturality of the derived unit transport** in the complex. -/
lemma derivedUnitTransport_naturality {G G' T S : Scheme.{u}} (s : G ⟶ G') {p : G' ⟶ T}
    {q : G' ⟶ S} {p₁ : G ⟶ T} {q₁ : G ⟶ S} (hp : s ≫ p = p₁) (hq : s ≫ q = q₁)
    {A A' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))}
    (e : A ⟶ A') :
    R((p)_*⟦Λ⟧).map (L((q)^*⟦Λ⟧).map e) ≫ derivedUnitTransport Λ s hp hq A' =
      derivedUnitTransport Λ s hp hq A ≫ R((p₁)_*⟦Λ⟧).map (L((q₁)^*⟦Λ⟧).map e) := by
  subst hp hq
  have h (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) :
      derivedUnitTransport Λ s rfl rfl B = (derivedUnitTransportNatTrans Λ s p q).app B := by
    rw [derivedUnitTransport_rfl]
    simp only [derivedUnitTransportNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    rfl
  rw [h, h]
  exact (derivedUnitTransportNatTrans Λ s p q).naturality e

end CondensedRing

namespace GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))
  (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
  (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))

/-- The levelwise normalized trace `g_{∞*} g_∞^* K ⟶ K` of a complex. -/
noncomputable def complexTrace :
    (((ginf)_*⟦Λ⟧).mapHomologicalComplex _).obj
      ((((ginf)^*⟦Λ⟧).mapHomologicalComplex _).obj K) ⟶ K where
  f n := T.trace Λ (K.X n) hd (hc n)
  comm' i j _ := (T.map_comp_trace Λ hd (K.d i j) (hc i) (hc j)).symm

lemma unit_comp_complexTrace :
    ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K ≫
      T.complexTrace Λ hd K hc = 𝟙 K := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  exact T.unit_comp_trace Λ (K.X n) hd (hc n)

lemma unitTransport_comp_complexTrace (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf)
    (hσj : ∀ j, ∃ a, σ ≫ T.π j = T.π j ≫ T.ρ j a) :
    (NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K ≫
      T.complexTrace Λ hd K hc = T.complexTrace Λ hd K hc := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f]
  have h := T.infAction_comp_trace Λ (K.X n) hd (hc n) σ hσ hσj
  rw [infAction_eq] at h
  exact h

include hd hc in
/-- **An invariant retraction of the derived unit of a Galois tower.** For a bounded below complex
`K` such that at every term `g_{∞*} g_∞^* Kⁿ` is the colimit of the finite levels and `g_∞^* Kⁿ` is
`g_{∞*}`-acyclic, the derived unit `K ⟶ Rg_{∞*} Lg_∞^* K` has a retraction which is invariant
under the derived unit transports along the automorphisms of `Y_∞` over `X` compatible with the
Galois actions. -/
theorem exists_invariant_retraction_derivedUnit (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n))) :
    ∃ R : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj (DerivedCategory.Q.obj K)) ⟶
        DerivedCategory.Q.obj K,
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app
          (DerivedCategory.Q.obj K) ≫ R =
          𝟙 _ ∧
        ∀ (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf),
          (∀ j, ∃ a, σ ≫ T.π j = T.π j ≫ T.ρ j a) →
            derivedUnitTransport Λ σ hσ hσ (DerivedCategory.Q.obj K) ≫ R = R := by
  refine ⟨Adjunction.derivedUnitRetraction K a hK (T.complexTrace Λ hd K hc),
    Adjunction.derivedAdjunction_unit_app_comp_derivedUnitRetraction K a hK _
      (CondensedRing.upperStarLowerStarAdjunction Λ ginf) (T.unit_comp_complexTrace Λ hd K hc),
    fun σ hσ hσj ↦ ?_⟩
  have h := derivedUnitIso_hom_comp_derivedUnitTransport_self Λ ginf σ hσ K a hK
  rw [Adjunction.derivedUnitRetraction, ← cancel_epi
    (Adjunction.derivedUnitIso (f := (ginf)^*⟦Λ⟧) (g := (ginf)_*⟦Λ⟧) K a hK).hom,
    reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc]
  erw [← Functor.map_comp, T.unitTransport_comp_complexTrace Λ hd K hc σ hσ hσj]

include hd hc in
/-- `GaloisTower.exists_invariant_retraction_derivedUnit` for an object `C ≅ K` of the derived
category. -/
theorem exists_invariant_retraction_derivedUnit_of_iso (a : ℤ) [K.IsStrictlyGE a]
    (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (e : DerivedCategory.Q.obj K ≅ C) :
    ∃ R : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj C) ⟶ C,
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.app C ≫ R = 𝟙 _ ∧
        ∀ (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf),
          (∀ j, ∃ a, σ ≫ T.π j = T.π j ≫ T.ρ j a) →
            derivedUnitTransport Λ σ hσ hσ C ≫ R = R := by
  obtain ⟨R, hR₁, hR₂⟩ := T.exists_invariant_retraction_derivedUnit Λ hd K hc a hK
  refine ⟨R((ginf)_*⟦Λ⟧).map (L((ginf)^*⟦Λ⟧).map e.inv) ≫ R ≫ e.hom, ?_, fun σ hσ hσj ↦ ?_⟩
  · have hn := (CondensedRing.derivedUpperStarLowerStarAdjunction Λ ginf).unit.naturality e.inv
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp [reassoc_of% hR₁]
  · have hn := derivedUnitTransport_naturality Λ σ hσ hσ e.inv
    rw [← reassoc_of% hn, reassoc_of% (hR₂ σ hσ hσj)]

end GaloisTower

end AlgebraicGeometry.ProEtale
