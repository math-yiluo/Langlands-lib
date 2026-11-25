/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorQuotientContraction
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorRestrictionMateModel
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # Tensoring the restricted quotient tower

Source: Stacks Project, Tags 03CZ, 06YY and 07A4; the coefficient-unit calculation in
`thm-coef-integral-verdier.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ v₁ v₂
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom

private def tensorMate
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
    (μ : T ⋙ F ≅ F.prod F ⋙ S) :
    (𝟭 C).prod (F ⋙ U) ⋙ T ⟶ T ⋙ F ⋙ U :=
  Functor.whiskerLeft ((𝟭 C).prod (F ⋙ U) ⋙ T) adj.unit ≫
    Functor.whiskerRight (Functor.whiskerLeft ((𝟭 C).prod (F ⋙ U)) μ.hom) U ≫
    Functor.whiskerRight (Functor.whiskerRight
      (NatTrans.prod (𝟙 F) (Functor.whiskerLeft F adj.counit)) S) U ≫
    Functor.whiskerRight μ.inv U

private theorem tensorMate_app
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
    (μ : T ⋙ F ≅ F.prod F ⋙ S) (K V : C) :
    (tensorMate T S F U adj μ).app (K, V) =
      adj.homEquiv _ _ (μ.hom.app (K, U.obj (F.obj V)) ≫
        S.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj V))) ≫
        μ.inv.app (K, V)) := by
  simp only [tensorMate, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app,
    Adjunction.homEquiv_apply, Functor.map_comp]
  rfl

private theorem transportTransition
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (q : C ⥤ D) (T : C ⥤ C) (A : D ⥤ D)
    (F G : C ⥤ C) (LF LG : D ⥤ D)
    (τ : G ⟶ F) (t : LG ⟶ LF)
    (e : T ⋙ q ≅ q ⋙ A)
    (cF : ∀ Z, LF.obj (q.obj Z) ⟶ q.obj (F.obj Z))
    (cG : ∀ Z, LG.obj (q.obj Z) ⟶ q.obj (G.obj Z))
    (Z : C) (bF : T.obj (F.obj Z) ⟶ F.obj (T.obj Z))
    (bG : T.obj (G.obj Z) ⟶ G.obj (T.obj Z))
    (rF : A.obj (LF.obj (q.obj Z)) ⟶ LF.obj (A.obj (q.obj Z)))
    (rG : A.obj (LG.obj (q.obj Z)) ⟶ LG.obj (A.obj (q.obj Z)))
    [Mono (cF (T.obj Z))]
    (hZ : t.app (q.obj Z) ≫ cF Z = cG Z ≫ q.map (τ.app Z))
    (hT : t.app (q.obj (T.obj Z)) ≫ cF (T.obj Z) =
      cG (T.obj Z) ≫ q.map (τ.app (T.obj Z)))
    (hF : A.map (cF Z) ≫ e.inv.app (F.obj Z) ≫ q.map bF =
      rF ≫ LF.map (e.inv.app Z) ≫ cF (T.obj Z))
    (hG : A.map (cG Z) ≫ e.inv.app (G.obj Z) ≫ q.map bG =
      rG ≫ LG.map (e.inv.app Z) ≫ cG (T.obj Z))
    (hb : T.map (τ.app Z) ≫ bF = bG ≫ τ.app (T.obj Z)) :
    A.map (t.app (q.obj Z)) ≫ rF = rG ≫ t.app (A.obj (q.obj Z)) := by
  apply (cancel_mono (LF.map (e.inv.app Z))).1
  apply (cancel_mono (cF (T.obj Z))).1
  simp only [Category.assoc]
  calc
    A.map (t.app (q.obj Z)) ≫ rF ≫ LF.map (e.inv.app Z) ≫ cF (T.obj Z) =
        A.map (t.app (q.obj Z)) ≫
          (A.map (cF Z) ≫ e.inv.app (F.obj Z) ≫ q.map bF) := by
      rw [hF]
    _ = A.map (cG Z) ≫ A.map (q.map (τ.app Z)) ≫
        e.inv.app (F.obj Z) ≫ q.map bF := by
      rw [← A.map_comp_assoc, hZ, A.map_comp]
      simp only [Category.assoc]
    _ = A.map (cG Z) ≫ e.inv.app (G.obj Z) ≫
        q.map (T.map (τ.app Z) ≫ bF) := by
      rw [q.map_comp]
      have h := e.inv.naturality (τ.app Z)
      dsimp only [Functor.comp_map] at h
      simpa only [Category.assoc] using
        congrArg (fun k ↦ A.map (cG Z) ≫ k ≫ q.map bF) h
    _ = A.map (cG Z) ≫ e.inv.app (G.obj Z) ≫
        q.map (bG ≫ τ.app (T.obj Z)) := by rw [hb]
    _ = rG ≫ LG.map (e.inv.app Z) ≫ cG (T.obj Z) ≫
        q.map (τ.app (T.obj Z)) := by
      simpa only [q.map_comp, Category.assoc] using
        congrArg (fun k ↦ k ≫ q.map (τ.app (T.obj Z))) hG
    _ = rG ≫ t.app (A.obj (q.obj Z)) ≫
        LF.map (e.inv.app Z) ≫ cF (T.obj Z) := by
      rw [← hT]
      have h := t.naturality (e.inv.app Z)
      simpa only [Category.assoc, Functor.comp_obj] using
        congrArg (fun k ↦ rG ≫ k ≫ cF (T.obj Z)) h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The canonical map from tensor with a restricted reduction to reduction of tensor.
It is constructed by the scalar adjunction, the normalized tensor comparison and its
inverse; no Hom object or dualizing complex occurs.
Source: Stacks 03CZ, 06YY and 07A4
(blueprint: lem-sf-integral-tensor-restriction-transition). -/
def restrictionTensor
    {a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl)}
    {n : ℕ} (m : ReductionPresentation l E X D hl a n)
    (K V : DerivedCategory (scalarReductionSource l E X)) :
    a.tensor.obj (K, (sfDerivedReductionRestricted l E X n).obj V) ⟶
      (sfDerivedReductionRestricted l E X n).obj (a.tensor.obj (K, V)) :=
  (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.homEquiv _ _
    (m.mu.hom.app (K, (sfDerivedReductionRestricted l E X n).obj V) ≫
      m.target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose.counit.app
            ((scalarReductionDerivedExtension l E X n).obj V))) ≫ m.mu.inv.app (K, V))

/-- Tensoring the second input commutes with the consecutive quotient transition.

Source: Stacks 03CZ, 06YY and 07A4; coefficient units and quotient maps for
evaluation-preserving reduction in the integral Verdier proof.

Proof: choose K-flat complexes P and Q representing K and V and a K-flat resolution
of the restricted finite reduction of Q. Apply the scalar adjunction to the displayed
map. Its counit multiplies the scalar factor and its tensor comparisons are fixed by
ReductionPresentation.normalization. Consequently, on a homogeneous tensor it is
x tensor (b tensor y) maps to b tensor (x tensor y), with b in degree zero. The two
routes across the consecutive quotient square therefore both send this tensor to
q(b) tensor (x tensor y), where q is the actual quotient map. Balanced pure tensors
generate the ordinary sheafified tensors, and the total tensor is a direct sum in
each degree, so these formulas give equality of chain maps. The representative
normalization of sfDerivedReductionTransition identifies these maps with the stated
transitions. Localize the equality and cancel the K-flat resolution and comparison
isomorphisms. This works in every degree and at n = 0 without boundedness or
constructibility assumptions.
(blueprint: lem-sf-integral-tensor-restriction-transition). -/
theorem restrictionTensor_transition
    (a : TensorPresentation.{u, u} X (completedIntegralCommRingSheaf l E X D hl))
    (m : ∀ n : ℕ, ReductionPresentation l E X D hl a n)
    (K V : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    a.tensor.map (Prod.mkHom (𝟙 K) ((sfDerivedReductionTransition l E X n).app V)) ≫
        restrictionTensor l E X D hl (m n) K V =
      restrictionTensor l E X D hl (m (n + 1)) K V ≫
        (sfDerivedReductionTransition l E X n).app (a.tensor.obj (K, V)) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let C := scalarReductionSource.{u, u} l E X
  let Qloc := DerivedCategory.Q.{u + 2, u + 1, u + 2} (C := C)
  let T := totalTensor.{u, u} X R
  let A := DerivedCategory C
  let F := fun j : ℕ ↦ (sfReductionRestricted l E X j).mapHomologicalComplex (.up ℤ)
  let LF := fun j : ℕ ↦ sfDerivedReductionRestricted l E X j
  let τ := sfDerivedReductionTransition l E X n
  let τ₀ := NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)
  let b (j : ℕ) : (𝟭 A).prod (LF j) ⋙ a.tensor ⟶ a.tensor ⋙ LF j :=
    tensorMate a.tensor (m j).target.tensor
      (scalarReductionDerivedExtension l E X j) (scalarReductionDerivedRestriction l E X j)
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X j).choose (m j).mu
  have hb (j : ℕ) (Z : A × A) :
      (b j).app Z = restrictionTensor l E X D hl (m j) Z.1 Z.2 := by
    exact tensorMate_app _ _ _ _ _ _ _ _
  let α : (𝟭 A).prod (LF (n + 1)) ⋙ a.tensor ⟶ a.tensor ⋙ LF n :=
    Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 A)) τ) a.tensor ≫ b n
  let β : (𝟭 A).prod (LF (n + 1)) ⋙ a.tensor ⟶ a.tensor ⋙ LF n :=
    b (n + 1) ≫ Functor.whiskerLeft a.tensor τ
  obtain ⟨c, hc, hstep⟩ := ordinaryTensorQuotient_contractions l E X
  have hrepr (P Q : CochainComplex C ℤ)
      (hP : flat.{u, u} X R P) (hQ : flat.{u, u} X R Q) :
      α.app (Qloc.obj P, Qloc.obj Q) = β.app (Qloc.obj P, Qloc.obj Q) := by
    obtain ⟨e, _, he⟩ := restrictionTensor_mate_model l E X D hl a P hP
    let AP := (Functor.curry.obj a.tensor).obj (Qloc.obj P)
    have hPQ : flat.{u, u} X R ((T.obj P).obj Q) := by
      exact coefficientTotalTensor_isKFlat.{u, u + 1, u} (Scheme.ProEt.topology X) R P Q hP hQ
    have : IsIso (sfReductionRepresentativeComparison l E X n ((T.obj P).obj Q)) :=
      sfComparison_isIso l E X n ((T.obj P).obj Q) hPQ
    have ht (Z : CochainComplex C ℤ) (hZ : flat.{u, u} X R Z) :
        τ.app (Qloc.obj Z) ≫ sfReductionRepresentativeComparison l E X n Z =
          sfReductionRepresentativeComparison l E X (n + 1) Z ≫ Qloc.map (τ₀.app Z) := by
      have hz' : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
          (J := Scheme.ProEt.topology X) (R := R) Z := hZ
      have h := (sfDerivedReductionTransition_existsUnique.{u} l E X n).exists.choose_spec Z hz'
      simpa only [τ, sfDerivedReductionTransition, Qloc, τ₀] using h
    have hmodel (j : ℕ) :
        AP.map (sfReductionRepresentativeComparison l E X j Q) ≫
            e.inv.app ((F j).obj Q) ≫ Qloc.map (c P Q j) =
          restrictionTensor l E X D hl (m j) (Qloc.obj P) (Qloc.obj Q) ≫
            (LF j).map (e.inv.app Q) ≫
            sfReductionRepresentativeComparison l E X j ((T.obj P).obj Q) := by
      exact he j (m j) (fun Q ↦ c P Q j) (fun Q ↦ hc P Q j) Q hQ
    have h := transportTransition Qloc (T.obj P) AP (F n) (F (n + 1)) (LF n) (LF (n + 1))
      τ₀ τ e (sfReductionRepresentativeComparison l E X n)
      (sfReductionRepresentativeComparison l E X (n + 1)) Q (c P Q n) (c P Q (n + 1))
      (restrictionTensor l E X D hl (m n) (Qloc.obj P) (Qloc.obj Q))
      (restrictionTensor l E X D hl (m (n + 1)) (Qloc.obj P) (Qloc.obj Q))
      (ht Q hQ) (ht ((T.obj P).obj Q) hPQ) (hmodel n) (hmodel (n + 1)) (hstep P Q n)
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, hb, AP, Functor.curry_obj_obj_map,
      Functor.curry_obj_obj_obj, NatTrans.prod, NatTrans.id_app, Functor.comp_obj,
      Functor.prod_obj, Functor.id_obj] using h
  have hfirst (Q : CochainComplex C ℤ) (hQ : flat.{u, u} X R Q) :
      Functor.whiskerLeft (Prod.sectL A (Qloc.obj Q)) α =
        Functor.whiskerLeft (Prod.sectL A (Qloc.obj Q)) β := by
    apply sfDerived_natTrans_ext l E X
    intro P hP
    exact hrepr P Q hP hQ
  have hsecond (K : A) :
      Functor.whiskerLeft (Prod.sectR K A) α =
        Functor.whiskerLeft (Prod.sectR K A) β := by
    apply sfDerived_natTrans_ext l E X
    intro Q hQ
    exact NatTrans.congr_app (hfirst Q hQ) K
  have hαβ : α = β := by
    apply NatTrans.ext
    funext Z
    exact NatTrans.congr_app (hsecond Z.1) Z.2
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, hb, NatTrans.prod, NatTrans.id_app, Functor.id_obj]
    using NatTrans.congr_app hαβ (K, V)

end WeilConjectures.IntegralHom
