/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.WContractible

/-!
# Pro-étale direct images along an algebraic field base change

Let `Ω / L` be an algebraic field extension, `h : G ⟶ Spec L` a scheme over `L` and
`g : G_Ω = G ×_L Ω ⟶ G` the base change. For every étale sheaf `F₀` of `Λ`-modules on `G`, the
pro-étale sheaf `g^* ν^* F₀` is acyclic for the pro-étale direct image `g_*`
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`).

By `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_of_isWContractibleRing`, it suffices to
show that the higher derived sections of `g^* ν^* F₀` over `W ×_G G_Ω` vanish, for `W` an object
of the pro-étale site of `G` whose underlying scheme is the spectrum of a w-contractible ring
`R`. By the comparison of pro-étale and étale cohomology, these are the étale cohomology groups
of `W ×_G G_Ω = W ×_L Ω`, the cofiltered limit of the affine schemes `W ×_L K` over the finite
subextensions `K` of `Ω / L`, with affine transition maps. By continuity of étale cohomology,
it suffices that the higher étale cohomology of each `W ×_L K` vanishes; and `W ×_L K` is finite
of finite presentation over `Spec R`, hence the spectrum of a w-contractible ring.

## Main definitions

- `AlgebraicGeometry.FiniteIntermediateField.overDiagram`: the diagram `K ↦ Spec K` of schemes
  over `Spec L`.
- `AlgebraicGeometry.FiniteIntermediateField.overCone`: the cone with point `Spec Ω` over it,
  a limit cone (`AlgebraicGeometry.FiniteIntermediateField.isLimitOverCone`).

## Main statements

- `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace FiniteIntermediateField

variable (L Ω : Type u) [Field L] [Field Ω] [Algebra L Ω]

/-- The structure morphism `Spec K' ⟶ Spec L` factors through `Spec K` for `K ≤ K'`. -/
@[reassoc (attr := simp)]
lemma specMap_comp_specMap_algebraMap {K K' : FiniteIntermediateField L Ω} (h : K ≤ K') :
    specMap h ≫ Spec.map (CommRingCat.ofHom (algebraMap L K.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap L K'.1)) := by
  rw [← Spec.map_comp]
  rfl

/-- The diagram `K ↦ Spec K` of the finite subextensions `K` of `Ω / L`, as schemes over
`Spec L`. -/
@[simps]
noncomputable def overDiagram : (FiniteIntermediateField L Ω)ᵒᵖ ⥤ Over (Spec (.of L)) where
  obj K := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L K.unop.1)))
  map f := Over.homMk (specMap (leOfHom f.unop)) (specMap_comp_specMap_algebraMap L Ω _)
  map_id K := Over.OverMorphism.ext ((specDiagram L Ω).map_id K)
  map_comp f g := Over.OverMorphism.ext ((specDiagram L Ω).map_comp f g)

/-- The structure morphism `Spec Ω ⟶ Spec L` factors through `Spec K`. -/
@[reassoc (attr := simp)]
lemma specMap_algebraMap_comp_specMap_algebraMap (K : FiniteIntermediateField L Ω) :
    Spec.map (CommRingCat.ofHom (algebraMap K.1 Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L K.1)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := by
  rw [← Spec.map_comp]
  rfl

/-- The cone with point `Spec Ω` over `overDiagram L Ω`. -/
@[simps]
noncomputable def overCone : Cone (overDiagram L Ω) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
  π :=
    { app K := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap K.unop.1 Ω)))
        (specMap_algebraMap_comp_specMap_algebraMap L Ω K.unop)
      naturality _ _ f := Over.OverMorphism.ext ((specCone L Ω).π.naturality f) }

variable [Algebra.IsAlgebraic L Ω]

/-- `Spec Ω` is the limit of the `Spec K`, `K` running over the finite subextensions of the
algebraic extension `Ω / L`, as schemes over `Spec L`. -/
noncomputable def isLimitOverCone : IsLimit (overCone L Ω) := by
  refine isLimitOfReflects (Over.forget _) ?_
  refine (IsLimit.equivOfNatIsoOfIso (G := overDiagram L Ω ⋙ Over.forget _)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_) (specCone L Ω) _ ?_) (isLimitSpecCone L Ω)
  · intro K K' f
    simp
  · exact Cone.ext (Iso.refl _) fun _ ↦ by simp

end FiniteIntermediateField

namespace ProEtale

open Scheme FiniteIntermediateField

variable (Λ : Type (u + 1)) [Ring Λ] {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω]

/-- For a finite extension `K / L` and a scheme `X` over `L` which is the spectrum of a
w-contractible ring, `Spec K ×_L X` is affine with w-contractible ring of global sections. -/
lemma isAffine_and_isWContractibleRing_pullback (K : FiniteIntermediateField L Ω)
    {X : Scheme.{u}} (a : X ⟶ Spec (.of L)) {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : X ≅ Spec R) :
    IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap L K.1))) a) ∧
      IsWContractibleRing Γ(pullback (Spec.map (CommRingCat.ofHom (algebraMap L K.1))) a, ⊤) := by
  have := K.2
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap L K.1))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have : Algebra.FinitePresentation L K.1 :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap L K.1))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 inferInstance)
  exact isAffine_and_isWContractibleRing_of_isFinite (pullback.snd _ a ≫ e.hom)

variable {G : Scheme.{u}} (h : G ⟶ Spec (.of L))

/-- Let `W` be an object of the pro-étale site of an `L`-scheme `G` whose underlying scheme is
the spectrum of a w-contractible ring. For an algebraic extension `Ω / L` with base change
`g : G_Ω ⟶ G` and an étale sheaf `F₀` on `G`, the higher derived sections of `g^* ν^* F₀` over
`W ×_G G_Ω` vanish.

These are the higher étale cohomology groups of `W ×_G G_Ω = W ×_L Ω` with coefficients in
`F₀`, the cofiltered limit of the `W ×_L K`, `K / L` finite, whose higher étale cohomology
vanishes since they are spectra of w-contractible rings. -/
theorem isZero_rightDerived_sectionsFunctor_pullback_upperStar_comparisonUpperStar_obj
    [Algebra.IsAlgebraic L Ω] (W : G.ProEt) (R : CommRingCat.{u}) [IsWContractibleRing R]
    (e : W.left ≅ Spec R) (F₀ : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero (((sectionsFunctor (ModuleCat.{u + 1} Λ)
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
        (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj W)).rightDerived
          (q + 1)).obj ((ProEtale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj
              ((comparisonUpperStar (ModuleCat.{u + 1} Λ) G).obj F₀))) := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap L Ω))
  set g := pullback.fst h ι
  set T := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj W
  refine isZero_rightDerived_sectionsFunctor_of_upperStar _ T _ _ ?_
  refine IsZero.of_iso ?_ (((globalSectionsFunctor _ T.left).rightDerived (q + 1)).mapIso
    ((ProEtale.upperStar _ T.hom).mapIso ((comparisonUpperStarCompUpperStarIso _ g).app F₀) ≪≫
      (comparisonUpperStarCompUpperStarIso _ T.hom).app _))
  refine isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj _ _ _ _ ?_
  refine IsZero.of_iso ?_ (((Etale.sectionsFunctor _ T.left).rightDerived (q + 1)).mapIso
    ((Etale.upperStarComp _ T.hom g).app F₀).symm)
  -- `T.left = W ×_G G_Ω` is the limit of the `W ×_L K` over `G`
  let a := W.hom ≫ h
  let D := overDiagram L Ω ⋙ Over.pullback a ⋙ Over.map W.hom
  let c₀ := (Over.map W.hom).mapCone ((Over.pullback a).mapCone (overCone L Ω))
  have hc₀ : IsLimit ((Over.forget G).mapCone c₀) :=
    isLimitOfPreserves (Over.forget W.left)
      (isLimitOfPreserves (Over.pullback a) (isLimitOverCone L Ω))
  let iso : c₀.pt ≅ Over.mk (T.hom ≫ g) :=
    Over.isoMk (pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso h ι W.hom).symm) (by
      simp only [c₀, T, g, a, Functor.mapCone_pt, Over.map_obj_left, Over.pullback_obj_left,
        Over.mk_left, Iso.trans_hom, Iso.symm_hom, Over.mk_hom, Category.assoc,
        MorphismProperty.Over.pullback_obj_hom, pullbackRightPullbackFstIso_inv_snd_fst,
        Over.map_obj_hom, Over.pullback_obj_hom]
      exact pullbackSymmetry_hom_comp_fst_assoc _ _ _)
  have hc : IsLimit ((Over.forget G).mapCone (c₀.extend iso.inv)) :=
    hc₀.ofIsoLimit ((Cone.functoriality _ (Over.forget G)).mapIso (Cone.extendIso c₀ iso))
  have hD (K : (FiniteIntermediateField L Ω)ᵒᵖ) :=
    isAffine_and_isWContractibleRing_pullback K.unop a e
  have (K : (FiniteIntermediateField L Ω)ᵒᵖ) : IsAffine (D.obj K).left := (hD K).1
  have (K : (FiniteIntermediateField L Ω)ᵒᵖ) : IsWContractibleRing Γ((D.obj K).left, ⊤) :=
    (hD K).2
  have {K K' : (FiniteIntermediateField L Ω)ᵒᵖ} (f : K ⟶ K') : IsAffineHom (D.map f).left :=
    isAffineHom_of_isAffine _
  exact Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit _ F₀ D (c₀.extend iso.inv)
    hc (q + 1) fun K ↦ isZero_rightDerived_etaleSectionsFunctor_of_isWContractibleRing Λ _ _ q

/-- **Higher direct images along an algebraic field base change vanish on sheaves of étale
origin.** Let `Ω / L` be an algebraic field extension, `h : G ⟶ Spec L` and
`g : G_Ω = G ×_L Ω ⟶ G` the base change. For every étale sheaf `F₀` of `Λ`-modules on `G`, the
pro-étale sheaf `g^* ν^* F₀` is acyclic for the pro-étale direct image `g_*`. -/
theorem rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj [Algebra.IsAlgebraic L Ω]
    (F₀ : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).rightAcyclic
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) G).obj F₀)) :=
  rightAcyclic_lowerStar_of_isWContractibleRing Λ _ _ fun W R _ e q ↦
    isZero_rightDerived_sectionsFunctor_pullback_upperStar_comparisonUpperStar_obj Λ h W R e F₀ q

/-- Variant of `rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj` for a pro-étale sheaf
`F` of étale origin on `G`: `g^* F` is acyclic for `g_*`. -/
theorem rightAcyclic_lowerStar_upperStar_of_etaleOrigin [Algebra.IsAlgebraic L Ω]
    {F : Sheaf (ProEt.topology G) (ModuleCat.{u + 1} Λ)}
    (hF : (comparisonUpperStar (ModuleCat.{u + 1} Λ) G).essImage F) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ)
      (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).rightAcyclic
        ((ProEtale.upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))).obj F) := by
  obtain ⟨F₀, ⟨e⟩⟩ := hF
  exact (ProEtale.lowerStar _ _).rightAcyclic.prop_of_iso ((ProEtale.upperStar _ _).mapIso e)
    (rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj Λ h F₀)

end ProEtale

end AlgebraicGeometry
