/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridgeData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Underived data for normalized native ringed tensor comparisons

This is the underived and evaluation-normalized part of the normalized complex
comparison.  It is separated so that the total-complex and localization clauses
can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem iso_of_natural_hom_equiv
    {C D : Type*} [Category* C] [Category* D] (E : C ≌ D) (A : C) (B : D)
    (h : ∀ I, (A ⟶ I) ≃ (B ⟶ E.functor.obj I))
    (hn : ∀ (I J : C) (f : A ⟶ I) (g : I ⟶ J),
      h J (f ≫ g) = h I f ≫ E.functor.map g) :
    ∃ e : E.functor.obj A ≅ B,
      ∀ (I : C) (f : A ⟶ I), e.inv ≫ E.functor.map f = h I f := by
  let v := h A (𝟙 A)
  let c := E.counitIso.app B
  let u := (h (E.inverse.obj B)).symm c.inv
  let r := E.functor.preimage (c.hom ≫ v)
  have hu : h (E.inverse.obj B) u = c.inv := (h _).apply_symm_apply _
  have hur : u ≫ r = 𝟙 A := by
    apply (h A).injective
    rw [hn, hu]
    simp [r, v]
  refine ⟨⟨E.functor.map u ≫ c.hom, v, ?_, ?_⟩, ?_⟩
  · calc
      (E.functor.map u ≫ c.hom) ≫ v = E.functor.map (u ≫ r) := by
        simp [r, Functor.map_comp, Category.assoc]
      _ = 𝟙 _ := by rw [hur, E.functor.map_id]
  · have hv := hn A (E.inverse.obj B) (𝟙 A) u
    simp only [Category.id_comp] at hv
    rw [← Category.assoc, ← hv, hu]
    exact c.inv_hom_id
  · intro I f
    simpa only [Category.id_comp] using (hn A I (𝟙 A) f).symm

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

abbrev nativeRingedTensorObjData (P Q : ProEtaleWeilSheaf k₀ l X) :=
  (SheafOfModules.monoidalCategory b.R).tensorObj (b.native.functor.obj Q)
    (b.native.functor.obj P)

/-- The underived comparison and its evaluation normalization.
Source: Stacks 06YS and 06YU (blueprint: lem-sf-native-weil-tensor-ringed-underived-data). -/
structure NativeWeilRingedTensorUnderivedData where
  underived (P Q : ProEtaleWeilSheaf k₀ l X) :
    b.native.functor.obj ((T.obj P).obj Q) ≅ nativeRingedTensorObjData b P Q
  uncurry (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    (underived P Q).inv ≫
        b.native.functor.map (((adj.adj P).homEquiv Q I).symm f) =
      (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction b.R (b.native.functor.obj P)).homEquiv
          (b.native.functor.obj Q) (b.native.functor.obj I)).symm
            (b.native.functor.map f ≫ b.nativeHom.hom.app (op P, I))

set_option linter.unusedSectionVars false in
/-- The underived comparison fixed by the native and ringed tensor-Hom adjunctions.
Source: Stacks 06YS and 06YU; the uniqueness-of-left-adjoints step in the native
tensor model proof (blueprint: lem-sf-native-weil-tensor-ringed-underived-data).

Proof: transport the native parameter adjunction through the additive equivalence
`b.native`, compare its right adjoint with the sheaf tensor-Hom adjunction by
`b.nativeHom`, and use uniqueness of left adjoints.  The counit identity is the
displayed uncurrying equation; naturality in the parameter gives the required
two-variable comparison.  The construction is independent of all derived data.
-/
theorem native_weil_tensor_ringed_underived_data :
    Nonempty (NativeWeilRingedTensorUnderivedData b T adj) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let h (P Q I : ProEtaleWeilSheaf k₀ l X) :
      ((T.obj P).obj Q ⟶ I) ≃
        (nativeRingedTensorObjData b P Q ⟶ b.native.functor.obj I) :=
    (((((adj.adj P).homEquiv Q I).trans b.native.fullyFaithfulFunctor.homEquiv).trans
      (b.nativeHom.app (op P, I)).homToEquiv).trans
        ((SheafOfModules.tensorHomAdjunction b.R
          (b.native.functor.obj P)).homEquiv
            (b.native.functor.obj Q) (b.native.functor.obj I)).symm).trans
      (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).symm.homFromEquiv
  have h_apply (P Q I : ProEtaleWeilSheaf k₀ l X) (f : (T.obj P).obj Q ⟶ I) :
      h P Q I f = (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction b.R (b.native.functor.obj P)).homEquiv
          (b.native.functor.obj Q) (b.native.functor.obj I)).symm
            (b.native.functor.map ((adj.adj P).homEquiv Q I f) ≫
              b.nativeHom.hom.app (op P, I)) := rfl
  have hn (P Q I I' : ProEtaleWeilSheaf k₀ l X)
      (f : (T.obj P).obj Q ⟶ I) (g : I ⟶ I') :
      h P Q I' (f ≫ g) = h P Q I f ≫ b.native.functor.map g := by
    have nh := b.nativeHom.hom.naturality
      (show (op P, I) ⟶ (op P, I') from (𝟙 _, g))
    dsimp only [Functor.comp_map, Functor.uncurry_obj_map, Functor.prod_map,
      Functor.op_map] at nh
    simp only [unop_id, CategoryTheory.Functor.map_id, op_id, NatTrans.id_app,
      Category.id_comp] at nh
    erw [(SheafOfModules.homFunctor b.R).map_id, NatTrans.id_app,
      Category.id_comp] at nh
    dsimp only [Functor.prod_obj, Functor.op_obj] at nh
    rw [h_apply, h_apply, Adjunction.homEquiv_naturality_right, Functor.map_comp,
      Category.assoc, nh, ← Category.assoc]
    have nt := (SheafOfModules.tensorHomAdjunction b.R
      (b.native.functor.obj P)).homEquiv_naturality_right_symm
        (b.native.functor.map ((adj.adj P).homEquiv Q I f) ≫
          b.nativeHom.hom.app (op P, I)) (b.native.functor.map g)
    simpa only [Category.assoc, Functor.prod_obj, nativeRingedTensorObjData] using
      congrArg ((β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫ ·) nt
  have he (P Q : ProEtaleWeilSheaf k₀ l X) :=
    iso_of_natural_hom_equiv b.native ((T.obj P).obj Q)
      (nativeRingedTensorObjData b P Q) (h P Q) (hn P Q)
  refine ⟨{ underived := fun P Q ↦ (he P Q).choose, uncurry := ?_ }⟩
  intro P Q I f
  rw [(he P Q).choose_spec I (((adj.adj P).homEquiv Q I).symm f)]
  rw [h_apply, Equiv.apply_symm_apply]

end AlgebraicGeometry.ProEtaleWeilSheaf
