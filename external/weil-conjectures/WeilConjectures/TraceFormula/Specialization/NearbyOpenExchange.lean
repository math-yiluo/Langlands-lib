/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchangeComposition
public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.OpenImmersionLowerShriekComp

/-!

# The exchanges of an open sub-model

For an open sub-model `N ⊆ M` of nearby-cycles models over open immersions `j : Y ⟶ X`,
`j' : Y' ⟶ X'`, with invertible pullback exchange `α_j : j'^* Ψ_M ⟶ Ψ_N j^*`, this file builds the
exchange `ν_j : Rj'_! Ψ_N ⟶ Ψ_M Rj_!` adjoint to `α_j⁻¹`
(`ProEtale.CondensedRing.NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange`) and shows:

* its exceptional adjoint is `β_j = α_j⁻¹` through `Rj^! ≅ j^*`
  (`NearbyCyclesModel.Hom.exceptionalExchange_boundedConstructibleLowerShriekExchange_app`
  );
* a compactification `M ⊆ P` of a trait model over the base restricts to a compactification
  `N ⊆ P` (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.ofOpen`), along which the
  compact-support exchange of `N` is the composite of `ν_j` and of the compact-support exchange
  of `M`
  (`NearbyCyclesModel.IsTraitModelOfBase.Compactification.compactSupportExchange_ofOpen_app`).
  This is the composition law of the compact-support exchanges
  (`ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app`), from the
  composition law `ν_{jι} = ι'_!(ν_j) ∘ ν_ι(j_!)` of the exchanges of open immersions
  (`ProEtale.CondensedRing.NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_openImmersion_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section OpenExchange

variable (ℓ : ℕ) [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (φ : N.Hom M j.left j'.left)
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- The components of `lowerShriekExchangeOfInv`. -/
lemma lowerShriekExchangeOfInv_app {DC DC' DP DP' : Type*} [Category DC] [Category DC']
    [Category DP] [Category DP'] {ΨC : DC ⥤ DC'} {ΨP : DP ⥤ DP'} {Dh : DC ⥤ DP} {Lh : DP ⥤ DC}
    {Dh' : DC' ⥤ DP'} {Lh' : DP' ⥤ DC'} (adj : Dh ⊣ Lh) (adj' : Dh' ⊣ Lh')
    (α : ΨP ⋙ Lh' ⟶ Lh ⋙ ΨC) [IsIso α] (K : DC) :
    (lowerShriekExchangeOfInv adj adj' α).app K =
      Dh'.map (ΨC.map (adj.unit.app K) ≫ (inv α).app (Dh.obj K)) ≫
        adj'.counit.app (ΨP.obj (Dh.obj K)) := by
  simp [lowerShriekExchangeOfInv]

instance [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    IsIso (φ.boundedConstructiblePullbackExchange ℓ hN hM) := by
  have (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
      IsIso ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app K) := by
    have : IsIso ((ObjectProperty.ι _).map ((φ.boundedConstructiblePullbackExchange ℓ hN hM).app
        K)) := by
      rw [ObjectProperty.ι_map, NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom]
      infer_instance
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  exact NatIso.isIso_of_isIso_app _

/-- The exchange `ν_j : j'_! Ψ_N ⟶ Ψ_M j_!` of an open immersion of models on bounded
constructible complexes, adjoint to the inverse of the pullback exchange. -/
noncomputable def NearbyCyclesModel.Hom.boundedConstructibleOpenExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j' ⟶
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        NearbyCyclesModel.boundedConstructibleNearbyCycles hM :=
  lowerShriekExchangeOfInv
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
    (φ.boundedConstructiblePullbackExchange ℓ hN hM)

omit [IsOpenImmersion j.left] [IsOpenImmersion j'.left] in
/-- The components of the inverse of the restricted pullback exchange are those of the inverse of
the ambient one. -/
lemma NearbyCyclesModel.Hom.inv_boundedConstructiblePullbackExchange_app_hom
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((inv (φ.boundedConstructiblePullbackExchange ℓ hN hM)).app K).hom =
      (inv (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj := by
  rw [NatIso.isIso_inv_app (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)) K.obj]
  refine IsIso.eq_inv_of_hom_inv_id ?_
  rw [← NearbyCyclesModel.Hom.boundedConstructiblePullbackExchange_app_hom ℓ φ hN hM,
    ← ObjectProperty.FullSubcategory.comp_hom, ← NatTrans.comp_app, IsIso.hom_inv_id]
  rfl

/-- The components of `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` on the ambient
derived categories are those of the exchange adjoint to the inverse of the ambient pullback
exchange. -/
lemma NearbyCyclesModel.Hom.boundedConstructibleOpenExchange_app_hom
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructibleOpenExchange ℓ hN hM).app K).hom =
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
        (openImmersionAdjunction ℓ j'.left)
        (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj := by
  rw [NearbyCyclesModel.Hom.boundedConstructibleOpenExchange, lowerShriekExchangeOfInv_app,
    lowerShriekExchangeOfInv_app]
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleOpenImmersionLowerShriek_map_hom,
    boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
    NearbyCyclesModel.Hom.inv_boundedConstructiblePullbackExchange_app_hom]
  rw [← openImmersionLowerShriekUpperStarAdjunction_unit_app_hom]
  rfl

/-- The exchange `ν_j : Rj'_! Ψ_N ⟶ Ψ_M Rj_!` of an open immersion of models on bounded
constructible complexes: `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` read through
the identifications `Rj_! ≅ j_!` of the lower shrieks of open immersions. -/
noncomputable def NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    NearbyCyclesModel.boundedConstructibleNearbyCycles hN ⋙ boundedConstructibleLowerShriek ℓ j' ⟶
      boundedConstructibleLowerShriek ℓ j ⋙ NearbyCyclesModel.boundedConstructibleNearbyCycles hM :=
  Functor.whiskerLeft _ (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      j').hom ≫ φ.boundedConstructibleOpenExchange ℓ hN hM ≫
    Functor.whiskerRight (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      j).inv _

/-- The components of `NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange` on the
ambient derived categories: `Rj'_! ≅ j'_!`, the exchange adjoint to the inverse of the ambient
pullback exchange, and `Ψ_M` of `j_! ≅ Rj_!`. -/
lemma NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange_app_hom
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K).hom =
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom ≫
        (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
          (openImmersionAdjunction ℓ j'.left)
          (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj ≫
        (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
            K).hom := by
  simp only [NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NearbyCyclesModel.Hom.boundedConstructibleOpenExchange_app_hom]
  rfl

/-- The mate of `NearbyCyclesModel.Hom.boundedConstructibleOpenExchange` is the inverse of the
pullback exchange. -/
lemma NearbyCyclesModel.Hom.mateEquiv_boundedConstructibleOpenExchange
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    mateEquiv (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
        (φ.boundedConstructibleOpenExchange ℓ hN hM) =
      inv (φ.boundedConstructiblePullbackExchange ℓ hN hM) := by
  rw [NearbyCyclesModel.Hom.boundedConstructibleOpenExchange,
    lowerShriekExchangeOfInv_eq_mateEquiv_symm, Equiv.apply_symm_apply]

/-- `Rj^! ≅ Lj^*` is the conjugate of `Rj_! ≅ j_!`. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv
    {V W : Over (Spec (.of k))} [LocallyOfFiniteType V.hom] [QuasiCompact V.hom]
    [IsSeparated V.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (f : V ⟶ W) [IsOpenImmersion f.left] :
    boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ f =
      conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ f)
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f).symm := by
  unfold boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl
  rfl

/-- **The exceptional exchange of an open immersion of models is the inverse of the pullback
exchange**, through the identifications `Rj^! ≅ j^*`: `β_j = α_j⁻¹`. -/
lemma NearbyCyclesModel.Hom.exceptionalExchange_boundedConstructibleLowerShriekExchange_app
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (A : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (exceptionalExchange ℓ j j' (φ.boundedConstructibleLowerShriekExchange ℓ hN hM)).app A =
      (NearbyCyclesModel.boundedConstructibleNearbyCycles hN).map
          ((boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).hom.app A) ≫
        (inv (φ.boundedConstructiblePullbackExchange ℓ hN hM)).app A ≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hM).obj A) := by
  have h := mateEquiv_whiskerLeft_comp_comp_whiskerRight_app
      (boundedConstructibleUpperShriekAdjunction ℓ j)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
      (boundedConstructibleUpperShriekAdjunction ℓ j')
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j')
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j')
      (φ.boundedConstructibleOpenExchange ℓ hN hM) A
  rw [NearbyCyclesModel.Hom.mateEquiv_boundedConstructibleOpenExchange,
    ← boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv,
    ← boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl_eq_conjugateIsoEquiv] at h
  rw [exceptionalExchange, NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange]
  cast_proofs h

end OpenExchange

section Verdier

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {U X : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
  [IsSeparated U.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The two identifications `Rj^! ≅ Lj^*` of an open immersion agree. -/
lemma boundedConstructibleUpperShriekIsoUpperStar_eq_padicAlgCl (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    boundedConstructibleUpperShriekIsoUpperStar ℓ j =
      boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j := by
  have e : boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek ℓ j =
      boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j := by
    ext K
    simp only [boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek,
      boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl,
      boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl_eq', Iso.trans_hom,
      NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      ObjectProperty.FullSubcategory.comp_hom]
    erw [Category.id_comp]
  rw [boundedConstructibleUpperShriekIsoUpperStar, e]
  rfl

/-- The identification `Rj^! ω_X ≅ ω_U` of Verdier duality is the composition isomorphism of the
dualizing complexes. -/
lemma upperShriekDualizingComplexIso_eq_dualizingComplexComp (j : U ⟶ X) :
    upperShriekDualizingComplexIso ℓ j = dualizingComplexComp ℓ j :=
  rfl

end Verdier

section Composition

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {Y X Z : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- On the ambient derived categories, the composition isomorphism of the extensions by zero on
bounded constructible complexes is the conjugate of the composition isomorphism of the derived
pullbacks. -/
lemma boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom (j : Y ⟶ X) (ι : X ⟶ Z)
    [IsOpenImmersion j.left] [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
      ι).hom.app K).hom =
      (((conjugateIsoEquiv (openImmersionAdjunction ℓ (j ≫ ι).left)
        ((openImmersionAdjunction ℓ j.left).comp (openImmersionAdjunction ℓ ι.left))).symm
          (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j.left ι.left)).symm).hom.app
        K.obj := by
  simp only [boundedConstructibleOpenImmersionLowerShriekComp, Iso.symm_hom, conjugateIsoEquiv,
    Equiv.coe_fn_symm_mk, conjugateEquiv_symm_apply_app, ObjectProperty.FullSubcategory.comp_hom,
    boundedConstructibleOpenImmersionLowerShriek_map_hom, Adjunction.comp_unit_app,
    openImmersionLowerShriekUpperStarAdjunction_unit_app_hom, boundedConstructibleUpperStar_map_hom,
    upperStarComp_inv_app_hom,
    boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_counit_app_hom,
    Functor.map_comp]
  rfl

/-- **The associativity of the composition isomorphisms of the lower shriek**, for morphisms equal
to composites. -/
lemma lowerShriekCompOfEq_hom_app_comp_hom_app {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z)
    (p : Z ⟶ S) {a : X ⟶ S} {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b)
    (wjι : (j ≫ ι) ≫ p = b) (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekCompOfEq ℓ j a wb).hom.app L ≫
        (lowerShriekCompOfEq ℓ ι p wa).hom.app ((boundedConstructibleLowerShriek ℓ j).obj L) =
      (lowerShriekCompOfEq ℓ (j ≫ ι) p wjι).hom.app L ≫
        (boundedConstructibleLowerShriek ℓ p).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι).hom.app L) := by
  subst wa wb
  have h := boundedConstructibleLowerShriekComp_padicAlgCl_assoc ℓ j ι p L
  simp only [lowerShriekCompOfEq, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
    Category.assoc] at h ⊢
  rw [h]
  simp

/-- The diagram chase behind
`compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp`, in abstract
categories. -/
lemma compactificationLowerShriekIso_comp_aux {A B C S : Type*} [Category A] [Category B]
    [Category C] [Category S] {Lb : A ⥤ S} {Lj oj : A ⥤ B} {La : B ⥤ S} {Ljι ojι : A ⥤ C}
    {Lι oι : B ⥤ C} {Lp Pp : C ⥤ S} (c₁ : Lb ≅ Ljι ⋙ Lp) (c₂ : Lb ≅ Lj ⋙ La)
    (c₃ : La ≅ Lι ⋙ Lp) (c : Ljι ≅ Lj ⋙ Lι) (ij : Lj ≅ oj) (iι : Lι ≅ oι) (ijι : Ljι ≅ ojι)
    (oc : ojι ≅ oj ⋙ oι) (ip : Lp ≅ Pp)
    (hassoc : ∀ L, c₂.hom.app L ≫ c₃.hom.app (Lj.obj L) = c₁.hom.app L ≫ Lp.map (c.hom.app L))
    (hA : ∀ L, c.hom.app L ≫ Lι.map (ij.hom.app L) ≫ iι.hom.app (oj.obj L) =
      ijι.hom.app L ≫ oc.hom.app L) (L : A) :
    (c₁ ≪≫ Functor.isoWhiskerRight ijι Lp ≪≫ Functor.isoWhiskerLeft ojι ip).hom.app L ≫
        Pp.map (oc.hom.app L ≫ oι.map (ij.inv.app L)) =
      c₂.hom.app L ≫
        (c₃ ≪≫ Functor.isoWhiskerRight iι Lp ≪≫ Functor.isoWhiskerLeft oι ip).hom.app
          (Lj.obj L) := by
  have hι := iι.hom.naturality (ij.inv.app L)
  have hp := ip.hom.naturality (oc.hom.app L ≫ oι.map (ij.inv.app L))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc]
  rw [← hp, reassoc_of% (hassoc L), ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  rw [← reassoc_of% (hA L), ← hι, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The factorizations of the lower shriek through a composite of open immersions**: for open
immersions `j`, `ι` and a proper `p`, the factorization `Rb_! ≅ (j ≫ ι)_! ⋙ Rp_*` followed by
`(j ≫ ι)_! ≅ j_! ⋙ ι_! ≅ Rj_! ⋙ ι_!` is the composition isomorphism `Rb_! ≅ Rj_! ⋙ Ra_!` followed
by the factorization `Ra_! ≅ ι_! ⋙ Rp_*`. -/
lemma compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp
    {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z) (p : Z ⟶ S) [IsOpenImmersion j.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] [IsProper p.left] {a : X ⟶ S}
    {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b) (wjι : (j ≫ ι) ≫ p = b)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactificationLowerShriekIso ℓ (j ≫ ι) p wjι).hom.app L ≫
        (boundedConstructibleLowerStar ℓ p).map
          ((boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j
            ι).hom.app L ≫
          (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ ι).map
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
              L)) =
      (lowerShriekCompOfEq ℓ j a wb).hom.app L ≫
        (compactificationLowerShriekIso ℓ ι p wa).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj L) := by
  have h := compactificationLowerShriekIso_comp_aux (lowerShriekCompOfEq ℓ (j ≫ ι) p wjι)
    (lowerShriekCompOfEq ℓ j a wb) (lowerShriekCompOfEq ℓ ι p wa)
    (boundedConstructibleLowerShriekComp_padicAlgCl ℓ j ι)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ ι)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ (j ≫ ι))
    (boundedConstructibleOpenImmersionLowerShriekComp (Profinite.padicAlgClRingObj ℓ) ℓ j ι)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ p)
    (fun L ↦ by cast_proofs lowerShriekCompOfEq_hom_app_comp_hom_app ℓ j ι p wa wb wjι L)
    (fun L ↦ by
      cast_proofs boundedConstructibleLowerShriekComp_padicAlgCl_hom_app_of_isOpenImmersion ℓ j ι
        L) L
  rw [compactificationLowerShriekIso, compactificationLowerShriekIso]
  cast_proofs h


omit [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] in
/-- The diagram chase behind
`compactificationLowerShriekIso_inv_app_comp_hom_app_hom`: from `h ≫ e = l ≫ g` for
isomorphisms `h`, `g`, `h⁻¹ ≫ l = e ≫ g⁻¹`. -/
private lemma inv_comp_eq_comp_inv_aux {C : Type*} [Category C] {a b c d : C} (hh : a ⟶ b)
    (hi : b ⟶ a) (l : a ⟶ c) (e : b ⟶ d) (gh : c ⟶ d) (gi : d ⟶ c) (h₁ : hi ≫ hh = 𝟙 b)
    (h₂ : gh ≫ gi = 𝟙 c) (hC : hh ≫ e = l ≫ gh) : hi ≫ l = e ≫ gi := by
  calc hi ≫ l = hi ≫ l ≫ gh ≫ gi := by rw [h₂, Category.comp_id]
    _ = e ≫ gi := by rw [← reassoc_of% hC, reassoc_of% h₁]

/-- `compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp` on the
ambient derived categories. -/
lemma compactificationLowerShriekIso_hom_app_hom_comp_map_openImmersionLowerShriekComp
    {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z) (p : Z ⟶ S) [IsOpenImmersion j.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] [IsProper p.left] {a : X ⟶ S}
    {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b) (wjι : (j ≫ ι) ≫ p = b)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((compactificationLowerShriekIso ℓ (j ≫ ι) p wjι).hom.app L).hom ≫
        R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j ι).hom.app L).hom ≫
            D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
                L).hom) =
      ((lowerShriekCompOfEq ℓ j a wb).hom.app L).hom ≫
        ((compactificationLowerShriekIso ℓ ι p wa).hom.app
          ((boundedConstructibleLowerShriek ℓ j).obj L)).hom := by
  have h := congrArg (fun f ↦ f.hom)
    (compactificationLowerShriekIso_hom_app_comp_map_openImmersionLowerShriekComp ℓ j ι p wa wb
      wjι L)
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedConstructibleLowerStar_map_hom] at h
  exact h

/-- `compactificationLowerShriekIso_hom_app_hom_comp_map_openImmersionLowerShriekComp` with the
inverses of the factorizations, written with the restricted functors as lifts of the ambient ones
as in `compactSupportExchangeOfCompactification_eq_lift`. -/
lemma compactificationLowerShriekIso_inv_app_comp_hom_app_hom
    {S : Over (Spec (.of k))} [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [IsSeparated S.hom] (j : Y ⟶ X) (ι : X ⟶ Z) (p : Z ⟶ S) [IsOpenImmersion j.left]
    [IsOpenImmersion ι.left] [IsOpenImmersion (j ≫ ι).left] [IsProper p.left] {a : X ⟶ S}
    {b : Y ⟶ S} (wa : ι ≫ p = a) (wb : j ≫ a = b) (wjι : (j ≫ ι) ≫ p = b)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (NatTrans.app (Iso.inv (X := boundedConstructibleLowerShriek ℓ b)
        (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            D(((j ≫ ι).left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ (j ≫ ι)).obj K).property) ⋙
          (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
            R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
            (fun K ↦ ((boundedConstructibleLowerStar ℓ p).obj K).property))
        (compactificationLowerShriekIso ℓ (j ≫ ι) p wjι)) L ≫
        (lowerShriekCompOfEq ℓ j a wb).hom.app L).hom =
      R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧).map
          (((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j ι).hom.app L).hom ≫
            D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
              ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
                L).hom) ≫
        (NatTrans.app (Iso.inv (X := boundedConstructibleLowerShriek ℓ a)
          (Y := (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
              D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
              (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι).obj K).property) ⋙
            (boundedConstructible _).lift ((boundedConstructible _).ι ⋙
              R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
              (fun K ↦ ((boundedConstructibleLowerStar ℓ p).obj K).property))
          (compactificationLowerShriekIso ℓ ι p wa))
          ((boundedConstructibleLowerShriek ℓ j).obj L)).hom := by
  rw [ObjectProperty.FullSubcategory.comp_hom]
  refine inv_comp_eq_comp_inv_aux ((compactificationLowerShriekIso ℓ (j ≫ ι) p wjι).hom.app L).hom
    _ _ _ ((compactificationLowerShriekIso ℓ ι p wa).hom.app
      ((boundedConstructibleLowerShriek ℓ j).obj L)).hom _ ?_ ?_
    (compactificationLowerShriekIso_hom_app_hom_comp_map_openImmersionLowerShriekComp ℓ j ι p wa
      wb wjι L)
  · rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  · rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    rfl
end Composition

section OpenComposition

/-- The diagram chase behind
`NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app_map_comp`. -/
private lemma comp_map_comp_eq_aux {C D : Type*} [Category C] [Category D] (Ψ : C ⥤ D)
    {x y z : C} {a e f g h : D} (νN : a ⟶ Ψ.obj x) (Eg Ec : x ⟶ y) (F : y ⟶ z) (E'g E'c : a ⟶ e)
    (ν₁ : e ⟶ f) (νA : f ⟶ Ψ.obj y) (Nm : f ⟶ h) (I' : e ⟶ g) (B : g ⟶ h) (νB : h ⟶ Ψ.obj z)
    (hE : Eg = Ec) (hE' : E'g = E'c) (hA : νN ≫ Ψ.map Ec = E'c ≫ ν₁ ≫ νA)
    (n : Nm ≫ νB = νA ≫ Ψ.map F) (hB : I' ≫ B = ν₁ ≫ Nm) :
    νN ≫ Ψ.map (Eg ≫ F) = (E'g ≫ I') ≫ B ≫ νB := by
  subst hE hE'
  rw [Ψ.map_comp, reassoc_of% hA, ← n]
  simp only [Category.assoc, reassoc_of% hB]

/-- `G(i) ∘ G(b) = G(ν) ∘ G(m)` for `b = i' ≫ ν ≫ m` with `i ≫ i' = 𝟙`. -/
private lemma map_comp_map_eq_aux {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {p q r s : C}
    (i : p ⟶ q) (i' : q ⟶ p) (ν : p ⟶ r) (m : r ⟶ s) (b : q ⟶ s) (hi : i ≫ i' = 𝟙 p)
    (hb : b = i' ≫ ν ≫ m) : G.map i ≫ G.map b = G.map ν ≫ G.map m := by
  rw [hb, ← G.map_comp, ← G.map_comp, reassoc_of% hi]

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {Y X Z : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Y' X' Z' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {N : NearbyCyclesModel Y.left Y'.left} {M : NearbyCyclesModel X.left X'.left}
  {P : NearbyCyclesModel Z.left Z'.left}
  {j : Y ⟶ X} {j' : Y' ⟶ X'} {ι : X ⟶ Z} {ι' : X' ⟶ Z'} [IsOpenImmersion j.left]
  [IsOpenImmersion j'.left] [IsOpenImmersion ι.left] [IsOpenImmersion ι'.left]
  [IsOpenImmersion (j ≫ ι).left] [IsOpenImmersion (j' ≫ ι').left]
  (φ : N.Hom M j.left j'.left) (ψ : M.Hom P ι.left ι'.left)
  [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
  [IsIso (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
  [IsIso ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ))]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
  [IsSeparated Y'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom] in
/-- **The composition law of the exchanges `ν_h` of open immersions of models** (blueprint
`prose-E-15`): `ν_{jι} = ι'_!(ν_j) ∘ ν_ι(j_!)` through the conjugates
`(j ≫ ι)_! ≅ j_! ⋙ ι_!` of the composition isomorphisms of the pullbacks. -/
theorem NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_openImmersion_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))) :
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ (j ≫ ι).left)
        (openImmersionAdjunction ℓ (j' ≫ ι').left)
        ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K ≫
      (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        ((((conjugateIsoEquiv (openImmersionAdjunction ℓ (j ≫ ι).left)
          ((openImmersionAdjunction ℓ j.left).comp (openImmersionAdjunction ℓ ι.left))).symm
            (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j.left ι.left)).symm).hom.app
              K) =
    (((conjugateIsoEquiv (openImmersionAdjunction ℓ (j' ≫ ι').left)
        ((openImmersionAdjunction ℓ j'.left).comp (openImmersionAdjunction ℓ ι'.left))).symm
          (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j'.left ι'.left)).symm).hom.app
            ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj K) ≫
      D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
          (openImmersionAdjunction ℓ j'.left)
          (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K) ≫
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
          (openImmersionAdjunction ℓ ι'.left)
          (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
        (D((j.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K) :=
  CondensedRing.lowerShriekExchangeOfInv_comp_app _ _ _ _ _ _ _ _ _ _ _
    (fun A ↦ φ.pullbackExchange_comp_app_of_eq (Profinite.padicAlgClRingObj ℓ) ψ (φ.comp ψ) rfl rfl
      rfl rfl A) K

/-- `NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_openImmersion_app` read through the
identifications `Rj_! ≅ j_!`: the first identity of the composition law of the compact-support
exchanges, with the composition of extensions by zero `(j ≫ ι)_! ≅ ι_! j_! ≅ ι_! Rj_!` on both
sides and the exchange `ν_j` of `NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange`. -/
lemma NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app_map_comp
    (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ (j ≫ ι).left)
        (openImmersionAdjunction ℓ (j' ≫ ι').left)
        ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj ≫
      (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        (((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j ι).hom.app K).hom ≫
          D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
            ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
              K).hom) =
    (((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j' ι').hom.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom ≫
        D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
          ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').inv.app
            ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom) ≫
      D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K).hom ≫
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
          (openImmersionAdjunction ℓ ι'.left)
          (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
        ((boundedConstructibleLowerShriek ℓ j).obj K).obj := by
  have hA := NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_openImmersion_app ℓ φ ψ K.obj
  have n := (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
    (openImmersionAdjunction ℓ ι'.left)
    (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).naturality
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app K).hom
  refine comp_map_comp_eq_aux (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ)) _ _
    ((((conjugateIsoEquiv (openImmersionAdjunction ℓ (j ≫ ι).left)
      ((openImmersionAdjunction ℓ j.left).comp (openImmersionAdjunction ℓ ι.left))).symm
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j.left ι.left)).symm).hom.app
          K.obj) _ _
    ((((conjugateIsoEquiv (openImmersionAdjunction ℓ (j' ≫ ι').left)
      ((openImmersionAdjunction ℓ j'.left).comp (openImmersionAdjunction ℓ ι'.left))).symm
        (leftDerivedUpperStarComp (Profinite.padicAlgClRingObj ℓ) j'.left ι'.left)).symm).hom.app
          ((N.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj K.obj))
    (D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((lowerShriekExchangeOfInv (openImmersionAdjunction ℓ j.left)
          (openImmersionAdjunction ℓ j'.left)
          (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app K.obj))
    ((lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
      (openImmersionAdjunction ℓ ι'.left)
      (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))).app
        (D((j.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj K.obj))
    (D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
      ((M.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app
          K).hom)) _ _ _ ?_ ?_ ?_ ?_ ?_
  · cast_proofs boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom ℓ j ι K
  · cast_proofs boundedConstructibleOpenImmersionLowerShriekComp_hom_app_hom ℓ j' ι'
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)
  · cast_proofs hA
  · cast_proofs n
  · refine map_comp_map_eq_aux _ _
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K)).hom _ _ _ ?_
      (NearbyCyclesModel.Hom.boundedConstructibleLowerShriekExchange_app_hom ℓ φ hN hM K)
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl

variable [IsProper (toPoint Z).left] [IsProper (toPoint Z').left]
  (hN : N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))
  {T : NearbyCyclesModel (point k).left (point k').left}
  (hS : T.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

/-- **The compact-support exchanges along an open immersion of compactified models** (blueprint
`prose-E-15`, compatibility of `ν` with composition): for open immersions of models
`φ : N ⟶ M` over `j`, `j'` and `ψ : M ⟶ P` over `ι`, `ι'`, with `P` proper over the base with
structure morphism `a` to the trait, the compact-support exchange of the compactification
`j ≫ ι : N ⊆ P` is the composite of `ν_j` (adjoint to `α_j⁻¹`) and of the compact-support exchange
of `ι : M ⊆ P`, through the composition isomorphisms `Rb_! ≅ Rj_! ⋙ Ra_!`.

An instance of `ProEtale.CondensedRing.compactSupportExchangeAux_lift_comp_app_of_heq`: the
first identity is
`NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app_map_comp`, the other two are
`compactificationLowerShriekIso_hom_app_hom_comp_map_openImmersionLowerShriekComp` and
`compactificationLowerShriekIso_inv_app_comp_hom_app_hom`. -/
theorem compactSupportExchangeOfCompactification_comp_app
    (a : P.Hom T (toPoint Z).left (toPoint Z').left)
    (ha : IsIsoOn (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      Z.left)).ι (a.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)))
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint (j ≫ ι))
        (comp_toPoint (j' ≫ ι')) (φ.comp ψ) a ha).app K ≫
      (NearbyCyclesModel.boundedConstructibleNearbyCycles hS).map
        ((lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j)).hom.app K) =
    (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')).hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj K) ≫
      (boundedConstructibleLowerShriek ℓ (toPoint X')).map
        ((φ.boundedConstructibleLowerShriekExchange ℓ hN hM).app K) ≫
      (compactSupportExchangeOfCompactification ℓ hM hS (comp_toPoint ι) (comp_toPoint ι') ψ a
        ha).app ((boundedConstructibleLowerShriek ℓ j).obj K) := by
  -- Fix the functors before elaborating the lifted isomorphisms and compatibility identities.
  have h := CondensedRing.compactSupportExchangeAux_lift_comp_app_of_heq
    (PC := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))
    (PC' := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y'.left))
    (PX := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (PX' := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X'.left))
    (PP := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left))
    (PP' := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z'.left))
    (Ps := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left))
    (Ps' := boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k').left))
    (ΨC := N.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (ΨX := M.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (ΨP := P.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (Ψs := T.nearbyCycles (Profinite.padicAlgClRingObj ℓ))
    (DhN := D(((j ≫ ι).left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
    (DhN' := D(((j' ≫ ι').left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
    (DhM := D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
    (DhM' := D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Rp := R(((toPoint Z).left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (Rp' := R(((toPoint Z').left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    (LSfN := boundedConstructibleLowerShriek ℓ (toPoint Y))
    (LSfN' := boundedConstructibleLowerShriek ℓ (toPoint Y'))
    (LSfM := boundedConstructibleLowerShriek ℓ (toPoint X))
    (LSfM' := boundedConstructibleLowerShriek ℓ (toPoint X'))
    (Dj := boundedConstructibleLowerShriek ℓ j)
    (Dj' := boundedConstructibleLowerShriek ℓ j')
    (Sp := NearbyCyclesModel.boundedConstructibleNearbyCycles hN)
    (SpX := NearbyCyclesModel.boundedConstructibleNearbyCycles hM)
    (Ts := NearbyCyclesModel.boundedConstructibleNearbyCycles hS)
    (fun K ↦ hN K.obj K.property) (fun K ↦ hM K.obj K.property) (fun K ↦ hS K.obj K.property)
    (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ (j ≫ ι)).obj K).property)
    (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ (j' ≫ ι')).obj K).property)
    (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι).obj K).property)
    (fun K ↦ ((boundedConstructibleOpenImmersionLowerShriek _ ℓ ι').obj K).property)
    (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint Z)).obj K).property)
    (fun K ↦ ((boundedConstructibleLowerStar ℓ (toPoint Z')).obj K).property)
    (compactificationLowerShriekIso ℓ (j' ≫ ι') (toPoint Z') (comp_toPoint (j' ≫ ι')))
    (compactificationLowerShriekIso ℓ (j ≫ ι) (toPoint Z) (comp_toPoint (j ≫ ι)))
    (compactificationLowerShriekIso ℓ ι' (toPoint Z') (comp_toPoint ι'))
    (compactificationLowerShriekIso ℓ ι (toPoint Z) (comp_toPoint ι))
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ (j ≫ ι).left)
      (openImmersionAdjunction ℓ (j' ≫ ι').left)
      ((φ.comp ψ).pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ ι.left)
      (openImmersionAdjunction ℓ ι'.left) (ψ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)))
    (a.pushforwardExchange (Profinite.padicAlgClRingObj ℓ)) ha
    (lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j))
    (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')) rfl rfl rfl
    (φ.boundedConstructibleLowerShriekExchange ℓ hN hM)
    (compactSupportExchangeOfCompactification ℓ hN hS (comp_toPoint (j ≫ ι))
      (comp_toPoint (j' ≫ ι')) (φ.comp ψ) a ha)
    (heq_of_eq (compactSupportExchangeOfCompactification_eq_lift (ι₃ := j ≫ ι) (ι₃' := j' ≫ ι') ℓ hN
      hS (φ.comp ψ) a ha))
    (compactSupportExchangeOfCompactification ℓ hM hS (comp_toPoint ι) (comp_toPoint ι') ψ a ha)
    (heq_of_eq (compactSupportExchangeOfCompactification_eq_lift (ι₃ := ι) (ι₃' := ι') ℓ hM hS ψ a
      ha)) (fun M ↦ ?_) K
  · cast_proofs h
  refine ⟨((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j ι).hom.app M).hom ≫
      D((ι.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).inv.app M).hom,
    ((boundedConstructibleOpenImmersionLowerShriekComp _ ℓ j' ι').hom.app
        ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)).hom ≫
      D((ι'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).map
        ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j').inv.app
          ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)).hom, ?_, ?_, ?_⟩
  · simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
    exact NearbyCyclesModel.Hom.lowerShriekExchangeOfInv_comp_app_map_comp ℓ φ ψ hN hM M
  · cast_proofs compactificationLowerShriekIso_hom_app_hom_comp_map_openImmersionLowerShriekComp
      ℓ j' ι' (toPoint Z') (comp_toPoint ι') (comp_toPoint j') (comp_toPoint (j' ≫ ι'))
      ((NearbyCyclesModel.boundedConstructibleNearbyCycles hN).obj M)
  · cast_proofs compactificationLowerShriekIso_inv_app_comp_hom_app_hom ℓ j ι (toPoint Z)
      (comp_toPoint ι) (comp_toPoint j) (comp_toPoint (j ≫ ι)) M

end OpenComposition

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {Y : Over (Spec (.of k))} {Y' : Over (Spec (.of k'))} {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X.left X'.left}
  {qM : M.total ⟶ trait k'} {gM : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {hM : M.IsTraitModelOfBase k qM gM}

/-- **A compactification of a model restricts to its open sub-models**: for an open sub-model
`N ⊆ M` over open immersions `j`, `j'` and a compactification `M ⊆ P` over `ι`, `ι'`, the
compactification `N ⊆ P` over `j ≫ ι`, `j' ≫ ι'`. -/
noncomputable def Compactification.ofOpen (C : hM.Compactification)
    (hN : N.IsTraitModelOfBase k q g) (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X')
    [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) : hN.Compactification where
  X := C.X
  X' := C.X'
  model := C.model
  qc := C.qc
  gc := C.gc
  isTraitModelOfBase := C.isTraitModelOfBase
  isPullback_ε := C.isPullback_ε
  ι := j ≫ C.ι
  ι' := j' ≫ C.ι'
  isOpenImmersion_ι := by
    rw [Over.comp_left]
    infer_instance
  isOpenImmersion_ι' := by
    rw [Over.comp_left]
    infer_instance
  hom := φ.comp C.hom
  isOpenImmersion_hom_total := by
    rw [NearbyCyclesModel.Hom.comp_total]
    infer_instance
  isPullback_hom_j := hφ.paste_horiz C.isPullback_hom_j
  q_eq := by rw [hq, NearbyCyclesModel.Hom.comp_total, Category.assoc, ← C.q_eq]
  g_eq := by rw [hg, NearbyCyclesModel.Hom.comp_generic, Category.assoc, ← C.g_eq]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']
  {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {hM : M.IsTraitModelOfBase k qM gM}

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom] in
/-- The compact-support exchange of the compactification `N ⊆ P` restricted from `M ⊆ P`. -/
lemma Compactification.compactSupportExchange_ofOpen (C : hM.Compactification)
    (hN : N.IsTraitModelOfBase k q g) (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X')
    [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM) [IsOpenImmersion (j ≫ C.ι).left]
    [IsOpenImmersion (j' ≫ C.ι').left]
    [IsIso ((φ.comp C.hom).pullbackExchange (Profinite.padicAlgClRingObj ℓ))] :
    (C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ =
      compactSupportExchangeOfCompactification ℓ (hN.preservesBoundedConstructible ℓ)
        (preservesBoundedConstructible_traitModel ℓ) (comp_toPoint (j ≫ C.ι))
        (comp_toPoint (j' ≫ C.ι')) (φ.comp C.hom) C.isTraitModelOfBase.toTrait
        (C.isIsoOn_pushforwardExchange ℓ) :=
  rfl

/-- **The compact-support exchanges along an open sub-model** (blueprint
`prose-E-15`, `lemma-compatibilities-base-change-maps` (3)): for an open sub-model `N ⊆ M`
over open immersions `j`, `j'` and a compactification `M ⊆ P`, the compact-support exchange of
the restricted compactification `N ⊆ P` is the composite of the exchange `ν_j` (adjoint to
`α_j⁻¹`) and of the compact-support exchange of `M ⊆ P`, through the composition isomorphisms
`Ra_N! ≅ Rj_! ⋙ Ra_M!` and `Ra'_N! ≅ Rj'_! ⋙ Ra'_M!`.

An instance of `ProEtale.CondensedRing.compactSupportExchangeOfCompactification_comp_app` at the
morphisms of models `φ : N ⟶ M` and `C.hom : M ⟶ P`. -/
theorem Compactification.compactSupportExchange_ofOpen_app (C : hM.Compactification)
    (hN : N.IsTraitModelOfBase k q g) (j : Y ⟶ X) [IsOpenImmersion j.left] (j' : Y' ⟶ X')
    [IsOpenImmersion j'.left] (φ : N.Hom M j.left j'.left) [IsOpenImmersion φ.total]
    (hφ : IsPullback φ.generic N.j M.j φ.total) (hq : q = φ.total ≫ qM)
    (hg : g = φ.generic ≫ gM)
    [IsIso (φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ))]
    (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((C.ofOpen hN j j' φ hφ hq hg).compactSupportExchange ℓ).app K ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          ((lowerShriekCompOfEq ℓ j (toPoint X) (comp_toPoint j)).hom.app K) =
      (lowerShriekCompOfEq ℓ j' (toPoint X') (comp_toPoint j')).hom.app
          ((boundedConstructibleNearbyCycles (hN.preservesBoundedConstructible ℓ)).obj K) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          ((φ.boundedConstructibleLowerShriekExchange ℓ (hN.preservesBoundedConstructible ℓ)
            (hM.preservesBoundedConstructible ℓ)).app K) ≫
        (C.compactSupportExchange ℓ).app ((boundedConstructibleLowerShriek ℓ j).obj K) := by
  have : IsOpenImmersion (j ≫ C.ι).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsOpenImmersion (j' ≫ C.ι').left := by
    rw [Over.comp_left]
    infer_instance
  have : IsIso ((φ.comp C.hom).pullbackExchange (Profinite.padicAlgClRingObj ℓ)) :=
    inferInstanceAs (IsIso ((C.ofOpen hN j j' φ hφ hq hg).hom.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)))
  cast_proofs compactSupportExchangeOfCompactification_comp_app ℓ φ C.hom
    (hN.preservesBoundedConstructible ℓ) (hM.preservesBoundedConstructible ℓ)
    (preservesBoundedConstructible_traitModel ℓ) C.isTraitModelOfBase.toTrait
    (C.isIsoOn_pushforwardExchange ℓ) K

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.IsTraitModelOfBase

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section DualizingComp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {F X : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {F' X' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {ΨF : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

/-- `ProEtale.CondensedRing.dualizingExchange_eq_comp` for the dualizing complexes
`ProEtale.CondensedRing.dualizingComplex` of Verdier duality. -/
theorem dualizingExchange_eq_comp_dualizingComplex (d : F ⟶ X) (d' : F' ⟶ X')
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ d' ⟶
      boundedConstructibleLowerShriek ℓ d ⋙ ΨX)
    (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)
    (νF : ΨF ⋙ boundedConstructibleLowerShriek ℓ (toPoint F') ⟶
      boundedConstructibleLowerShriek ℓ (toPoint F) ⋙ Ψpt)
    (h : ∀ M, νF.app M ≫
        Ψpt.map ((lowerShriekCompOfEq ℓ d (toPoint X) (comp_toPoint d)).hom.app M) =
      (lowerShriekCompOfEq ℓ d' (toPoint X') (comp_toPoint d')).hom.app (ΨF.obj M) ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X')).map
          (νd.app M) ≫
          νX.app ((boundedConstructibleLowerShriek ℓ d).obj M)) :
    @Eq (ΨF.obj (dualizingComplex ℓ F) ⟶ dualizingComplex ℓ F') (dualizingExchange ℓ σpt νF)
      (ΨF.map (Iso.inv (X := (boundedConstructibleUpperShriek ℓ d).obj (dualizingComplex ℓ X))
          (Y := dualizingComplex ℓ F) (dualizingComplexComp ℓ d)) ≫
        (exceptionalExchange ℓ d d' νd).app (dualizingComplex ℓ X) ≫
        (boundedConstructibleUpperShriek ℓ d').map
          (X := ΨX.obj (dualizingComplex ℓ X)) (Y := dualizingComplex ℓ X')
          (dualizingExchange ℓ σpt νX) ≫
        Iso.hom (X := (boundedConstructibleUpperShriek ℓ d').obj (dualizingComplex ℓ X'))
          (Y := dualizingComplex ℓ F') (dualizingComplexComp ℓ d')) :=
  dualizingExchange_eq_comp ℓ σpt d d' νd νX νF h

/-- The identification `ρ : Lj^* ω_X ≅ ω_U` of the dualizing complexes along an open immersion is
`Rj^! ≅ Lj^*` followed by the composition isomorphism of the dualizing complexes. -/
lemma dualizingComplexUpperStarIso_hom_eq {U Z : Over (Spec (.of k))}
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (i : U ⟶ Z)
    [IsOpenImmersion i.left] :
    (NearbyCyclesModel.dualizingComplexUpperStarIso ℓ i).hom =
      (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ i).inv.app
          (dualizingComplex ℓ Z) ≫ (dualizingComplexComp ℓ i).hom := by
  rw [NearbyCyclesModel.dualizingComplexUpperStarIso, dualizingComplexIsoUpperStar,
    boundedConstructibleUpperShriekIsoUpperStar_eq_padicAlgCl,
    upperShriekDualizingComplexIso_eq_dualizingComplexComp]
  simp

end DualizingComp

/-- The rearrangement behind the compatibility of the dualizing maps with open restriction. -/
lemma map_comp_eq_of_exceptionalExchange {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] {ΨM : B ⥤ B'} {ΨN : A ⥤ A'} {Lj Uj : B ⥤ A} {Lj' Uj' : B' ⥤ A'}
    (α : ΨM ⋙ Lj' ⟶ Lj ⋙ ΨN) [IsIso α] (u : Uj ≅ Lj) (u' : Uj' ≅ Lj')
    (β : Uj ⋙ ΨN ⟶ ΨM ⋙ Uj')
    (hβ : ∀ b, β.app b = ΨN.map (u.hom.app b) ≫ (inv α).app b ≫ u'.inv.app (ΨM.obj b))
    {ω : B} {ω' : B'} {ωY : A} {ωY' : A'} (θM : ΨM.obj ω ⟶ ω') (θN : ΨN.obj ωY ⟶ ωY')
    (d : Uj.obj ω ≅ ωY) (d' : Uj'.obj ω' ≅ ωY')
    (hθ : θN = ΨN.map d.inv ≫ β.app ω ≫ Uj'.map θM ≫ d'.hom) (ρ : Lj.obj ω ≅ ωY)
    (hρ : ρ.hom = u.inv.app ω ≫ d.hom) (ρ' : Lj'.obj ω' ≅ ωY')
    (hρ' : ρ'.hom = u'.inv.app ω' ≫ d'.hom) :
    Lj'.map θM ≫ ρ'.hom = α.app ω ≫ ΨN.map ρ.hom ≫ θN := by
  have n := u'.inv.naturality θM
  rw [hθ, hβ, hρ, hρ', reassoc_of% n]
  simp only [Functor.map_comp, Category.assoc]
  rw [← ΨN.map_comp_assoc d.hom d.inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, ← ΨN.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← NatTrans.comp_app_assoc, IsIso.hom_inv_id, NatTrans.id_app,
    Category.id_comp]

end AlgebraicGeometry.ProEtale.CondensedRing
