/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.NatIsoOfIsKInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The native internal hom out of a single pro-étale Weil sheaf

For a pro-étale Weil sheaf `A` placed in degree `d`, the native derived internal hom
`RHom(A[-d], -)` of pro-étale Weil sheaves (the internal hom of the closed structure
`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison`, right adjoint to the native
derived tensor product) is the right derived functor of `𝓗om(A, -)` followed by the shift `[d]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeWeilHomSingleIso`).

On a K-injective complex `I` the internal hom is the product-total hom complex
`∏_p 𝓗om(A[-d]^p, I^{p + n})`, which has only the factor `p = d`; projecting to it is an
isomorphism of complexes onto `𝓗om(A, I)[d]`
(`AlgebraicGeometry.ProEtaleWeilSheaf.singleHomProjection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The projection from the hom complex out of `A` placed in degree `d` to the factor `p = d`,
a morphism of complexes onto `𝓗om(A, I)[d]`. -/
noncomputable def singleHomProjection (A : ProEtaleWeilSheaf k₀ l X) (d : ℤ)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)
        ((CochainComplex.singleFunctor _ d).obj A) I ⟶
      (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I)⟦d⟧ where
  f k := CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ d).obj A) I k d (k + d) (add_comm d k) ≫
    ((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) d A).inv.op).app (I.X (k + d))
  comm' k k' _ := by
    rw [CochainComplex.shiftFunctor_obj_d', Category.assoc,
      CochainComplex.bifunctorHomObj_d_π_assoc _ _ _ k k' d (k' + d) (add_comm d k') (k + d)
        (k' + d - k) (add_comm d k) (by omega)]
    simp only [CochainComplex.singleFunctor_obj_d, op_zero, Functor.map_zero,
      NatTrans.app_zero, comp_zero, sub_zero, Functor.mapHomologicalComplex_obj_d,
      Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp]
    congr 1
    exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ d).obj A) I k d (k + d) (add_comm d k) ≫ ·)
      (((ihomBifunctor k₀ l X).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) d A).inv.op).naturality
          (I.d (k + d) (k' + d))).symm

/-- The projection to the factor `p = d` is an isomorphism of complexes: every other factor
`𝓗om(A[-d]^p, I^{p + n})`, `p ≠ d`, is zero. -/
instance isIso_singleHomProjection (A : ProEtaleWeilSheaf k₀ l X) (d : ℤ)
    (I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    IsIso (singleHomProjection A d I) := by
  classical
  have : ∀ k, IsIso ((singleHomProjection A d I).f k) := by
    intro k
    let j : ((((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I)⟦d⟧).X k ⟶
        (CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)
          ((CochainComplex.singleFunctor _ d).obj A) I).X k :=
      CochainComplex.bifunctorHomLift _ _ _ k fun p q hpq ↦
        if h : p = d then by
          subst p
          obtain rfl : q = k + d := by omega
          exact ((ihomBifunctor k₀ l X).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) d A).hom.op).app (I.X (k + d))
        else 0
    refine ⟨⟨j, ?_, ?_⟩⟩
    · apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      by_cases h : p = d
      · subst p
        obtain rfl : q = k + d := by omega
        simp only [singleHomProjection, j, Category.assoc,
          CochainComplex.bifunctorHomLift_π, ↓reduceDIte, ← NatTrans.comp_app,
          ← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
          (ihomBifunctor k₀ l X).map_id, NatTrans.id_app, Category.id_comp]
        erw [Category.comp_id]
      · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) d A p h
        have hz' := ((evaluation _ _).obj (I.X q)).map_isZero
          ((ihomBifunctor k₀ l X).map_isZero hz.op)
        exact hz'.eq_of_tgt _ _
    · simp [singleHomProjection, j, ← NatTrans.comp_app,
        ← Functor.map_comp, ← op_comp]
      rfl
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The projection to the factor `p = d` is natural in the target complex. -/
@[reassoc]
lemma bifunctorHomMapRight_singleHomProjection (A : ProEtaleWeilSheaf k₀ l X) (d : ℤ)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (g : I ⟶ I') :
    CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := (CochainComplex.singleFunctor _ d).obj A) g ≫ singleHomProjection A d I' =
      singleHomProjection A d I ≫
        (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g)⟦d⟧' := by
  apply HomologicalComplex.Hom.ext
  funext k
  simp only [singleHomProjection, HomologicalComplex.comp_f,
    CochainComplex.bifunctorHomMapRight_f_π_assoc, Category.assoc,
    CochainComplex.shiftFunctor_map_f', Functor.mapHomologicalComplex_map_f]
  exact congrArg (CochainComplex.bifunctorHomπ (ihomBifunctor k₀ l X)
      ((CochainComplex.singleFunctor _ d).obj A) I k d (k + d) (add_comm d k) ≫ ·)
    (((ihomBifunctor k₀ l X).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) d A).inv.op).naturality (g.f (k + d)))

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The naturality of the representative model of the native internal hom out of a fixed
complex `P`, in the K-injective target. -/
lemma nativeWeilHom_map_model_hom (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    {I I' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} [I.IsKInjective] [I'.IsKInjective]
    (g : I ⟶ I') :
    (Prod.sectR (op (DerivedCategory.Q.obj P)) _ ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom).map (DerivedCategory.Q.map g) ≫
      ((nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
        P I' inferInstance).hom =
    ((nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
        P I inferInstance).hom ≫
      DerivedCategory.Q.map (CochainComplex.bifunctorHomMapRight (H := ihomBifunctor k₀ l X)
        (K := P) g) := by
  have h := (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.naturality
    P P I I' inferInstance inferInstance (𝟙 _) g
  simp only [CategoryTheory.Functor.map_id, op_id, CochainComplex.bifunctorHomMapLeft_id,
    Category.id_comp] at h
  exact h

/-- **The native internal hom out of a single sheaf**: for a pro-étale Weil sheaf `A` placed in
degree `d`, the native derived internal hom `RHom(A[-d], -)` is `R𝓗om(A, -)[d]`, naturally. On a
K-injective complex `I` it is the hom complex into `I`
(`NativeHomRepresentatives.model`), projected to its only nonzero factor
(`AlgebraicGeometry.ProEtaleWeilSheaf.singleHomProjection`). -/
noncomputable def nativeWeilHomSingleIso (A : ProEtaleWeilSheaf k₀ l X) (d : ℤ) :
    Prod.sectR (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ d).obj A)))
        (DerivedCategory (ProEtaleWeilSheaf k₀ l X)) ⋙
        (nativeDerivedClosedComparison k₀ l X).homModels.weilHom ≅
      (ihomFunctor k₀ l X A).rightDerivedFunctor ⋙ shiftFunctor _ d :=
  DerivedCategory.natIsoOfIsKInjective _ _
    (fun I _ ↦ (nativeDerivedClosedComparison k₀ l X).homModels.weilRepresentatives.model
        _ I inferInstance ≪≫
      DerivedCategory.Q.mapIso (asIso (singleHomProjection A d I)) ≪≫
      (Functor.commShiftIso (DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)) d).app
        (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).obj I) ≪≫
      (shiftFunctor _ d).mapIso ((ihomFunctor k₀ l X A).rightDerivedFunctorObjQIso I).symm)
    (fun I I' _ _ g ↦ by
      have hM := CommSq.mk
        (nativeWeilHom_map_model_hom ((CochainComplex.singleFunctor _ d).obj A) g)
      have hP := (CommSq.mk (bifunctorHomMapRight_singleHomProjection A d g)).map
        DerivedCategory.Q
      have hS := CommSq.mk
        ((Functor.commShiftIso (DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X))
          d).hom.naturality (((ihomFunctor k₀ l X A).mapHomologicalComplex (.up ℤ)).map g))
      have hR := (CommSq.mk (Functor.rightDerivedFunctor_map_Q_map_comp_objQIso_inv
        (ihomFunctor k₀ l X A) g)).map (shiftFunctor _ d)
      simpa only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Iso.app_hom,
        Functor.comp_map] using (hM.vert_comp (hP.vert_comp (hS.vert_comp hR))).w)

end AlgebraicGeometry.ProEtaleWeilSheaf
