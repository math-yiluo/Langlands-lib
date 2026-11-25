/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerTrace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.LowerStar

/-!
# Continuity of derived pushforwards along a Galois tower

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `K` a bounded
below complex of `Λ_X`-module objects, `Λ = C(-, T₀)` for a finite discrete ring `T₀`. The
complexes `g_{j*} g_j^* K` of the finite levels form a filtered diagram with a cocone to
`g_{∞*} g_∞^* K` (`AlgebraicGeometry.ProEtale.GaloisTower.complexDiagram`,
`AlgebraicGeometry.ProEtale.GaloisTower.complexCocone`), which is a colimit when it is so termwise
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimitComplexCocone`). For a quasi-compact
quasi-separated `f : X ⟶ Z`, the cohomology sheaves of `Rf_*` of `g_{∞*} g_∞^* K` are then the
filtered colimits of those of the finite levels
(`AlgebraicGeometry.ProEtale.GaloisTower.isColimit_homology_rightDerivedLowerStar_complexCocone`):
the continuity of `Rf_* (g_{∞*} g_∞^*)` along the tower.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

instance (j : T.J) : (T.levelFunctor Λ j).Additive := by
  unfold levelFunctor
  infer_instance

instance : (infFunctor Λ ginf).Additive := by
  unfold infFunctor
  infer_instance

lemma transport_naturality {M M' : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X)} (φ : M ⟶ M') {j j' : T.J} (h : j ≤ j') :
    T.transport Λ M h ≫ (T.levelFunctor Λ j').map φ =
      (T.levelFunctor Λ j).map φ ≫ T.transport Λ M' h := by
  unfold transport
  exact ((unitTransport Λ (T.t h) (T.t_g h) (T.t_g h)).naturality φ).symm

variable (K : CochainComplex
  (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

/-- The transition map `g_{j*} g_j^* K ⟶ g_{j'*} g_{j'}^* K` of complexes. -/
noncomputable def complexTransport {j j' : T.J} (h : j ≤ j') :
    ((T.levelFunctor Λ j).mapHomologicalComplex _).obj K ⟶
      ((T.levelFunctor Λ j').mapHomologicalComplex _).obj K where
  f n := T.transport Λ (K.X n) h
  comm' i i' _ := T.transport_naturality Λ (K.d i i') h

/-- The map `g_{j*} g_j^* K ⟶ g_{∞*} g_∞^* K` of complexes. -/
noncomputable def complexInfTransport (j : T.J) :
    ((T.levelFunctor Λ j).mapHomologicalComplex _).obj K ⟶
      ((infFunctor Λ ginf).mapHomologicalComplex _).obj K where
  f n := T.infTransport Λ (K.X n) j
  comm' i i' _ := T.infTransport_naturality Λ (K.d i i') j

/-- The diagram of complexes `j ↦ g_{j*} g_j^* K`. -/
noncomputable def complexDiagram : T.J ⥤ CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ where
  obj j := ((T.levelFunctor Λ j).mapHomologicalComplex _).obj K
  map f := T.complexTransport Λ K (leOfHom f)
  map_id j := HomologicalComplex.hom_ext _ _ fun n ↦ T.transport_refl Λ (K.X n) j
  map_comp f f' := HomologicalComplex.hom_ext _ _ fun n ↦
    (T.transport_comp Λ (K.X n) (leOfHom f) (leOfHom f')).symm

/-- The cocone `g_{j*} g_j^* K ⟶ g_{∞*} g_∞^* K`. -/
noncomputable def complexCocone : Cocone (T.complexDiagram Λ K) where
  pt := ((infFunctor Λ ginf).mapHomologicalComplex _).obj K
  ι :=
    { app j := T.complexInfTransport Λ K j
      naturality _ _ f := HomologicalComplex.hom_ext _ _ fun n ↦
        (T.transport_comp_infTransport Λ (K.X n) (leOfHom f)).trans (comp_id _).symm }

lemma complexDiagram_map_f {j j' : T.J} (f : j ⟶ j') (n : ℤ) :
    ((T.complexDiagram Λ K).map f).f n = T.transport Λ (K.X n) (leOfHom f) := rfl

lemma complexCocone_ι_app_f (j : T.J) (n : ℤ) :
    ((T.complexCocone Λ K).ι.app j).f n = T.infTransport Λ (K.X n) j := rfl

/-- The diagram of the `n`-th terms of the complexes of the finite levels, on underlying sheaves, is
the diagram of restrictions of abelian sheaves. -/
noncomputable def evalForgetIso (n : ℤ) :
    (T.complexDiagram Λ K ⋙ HomologicalComplex.eval _ _ n) ⋙ Mod.forget _ ≅
      T.abDiagram (K.X n).X :=
  NatIso.ofComponents (fun j ↦ (T.g j)_*[Ab.{u + 1}].mapIso
      ((upperStarForgetIso Λ (T.g j)).app (K.X n)).symm) fun f ↦ by
    rw [Functor.comp_map, Functor.comp_map, HomologicalComplex.eval_map, complexDiagram_map_f,
      forget_map_transport]
    simp only [Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, abDiagram_map, assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, comp_id]

/-- **The colimit of the finite levels of a complex**: if the underlying abelian sheaf of
`g_{∞*} g_∞^* Kⁿ` is the colimit of the finite levels in every degree, then `g_{∞*} g_∞^* K` is
the colimit of the complexes of the finite levels. -/
noncomputable def isColimitComplexCocone (hc : ∀ n, IsColimit (T.abCocone (K.X n).X)) :
    IsColimit (T.complexCocone Λ K) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n ↦ ?_
  refine isColimitOfReflects (Mod.forget _)
    ((IsColimit.equivOfNatIsoOfIso (T.evalForgetIso Λ K n) _ _ ?_).symm (hc n))
  refine Cocone.ext ((ginf)_*[Ab.{u + 1}].mapIso
    ((upperStarForgetIso Λ _).app (K.X n)).symm) fun j ↦ ?_
  rw [Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app,
    Functor.mapCocone_ι_app, HomologicalComplex.eval_map, complexCocone_ι_app_f,
    forget_map_infTransport]
  simp only [evalForgetIso, NatIso.ofComponents_inv_app, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_inv, abCocone_ι_app,
    assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, comp_id]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]

/-- The complexes of the finite levels are bounded below as soon as `K` is. -/
instance (a : ℤ) [K.IsStrictlyGE a] (j : T.J) : ((T.complexDiagram Λ K).obj j).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi ↦
    (T.levelFunctor Λ j).map_isZero (CochainComplex.isZero_of_isStrictlyGE K a i hi)

/-- **Continuity of the derived pushforward along a Galois tower**: for `f : X ⟶ Z`
quasi-compact and quasi-separated and `K` bounded below with `g_{∞*} g_∞^* Kⁿ` the colimit of the
finite levels in every degree, the cohomology sheaves of `Rf_* (g_{∞*} g_∞^* K)` are the filtered
colimits of those of `Rf_* (g_{j*} g_j^* K)`. -/
theorem isColimit_homology_rightDerivedLowerStar_complexCocone (T₀ : Type) [TopologicalSpace T₀]
    [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀] [Finite T₀]
    (K : CochainComplex (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀) X)) ℤ)
    (hc : ∀ n, IsColimit (T.abCocone (K.X n).X))
    (a : ℤ) [K.IsStrictlyGE a] {Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ R((f)_*⟦Profinite.continuousMapRingObj T₀⟧) ⋙
      DerivedCategory.homologyFunctor _ q).mapCocone
        (T.complexCocone (Profinite.continuousMapRingObj T₀) K))) :=
  isColimit_mapCocone_homologyFunctor_rightDerivedFunctor_lowerStar T₀ f
    (T.complexDiagram (Profinite.continuousMapRingObj T₀) K) a
    (T.isColimitComplexCocone (Profinite.continuousMapRingObj T₀) K hc) q

end AlgebraicGeometry.ProEtale.GaloisTower
