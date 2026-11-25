/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData
public import WeilConjectures.WeilSheaf.Native.NativeFrobeniusRingedModel
public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality
import WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorInverseAssociativity
import WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryTensorSymmetry
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorTermwiseComparison
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryRelativeTensorIdentification
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorChainAssociativity
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Coherence of the canonical ordinary section-module comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
attribute [local instance] Mod.monoidalCategoryCochainComplex
attribute [local implicit_reducible] Mod.monoidalCategoryCochainComplex
  SheafOfModules.cochainModulesMonoidal

/-- Transport the specified Hom comparison through the inverse equivalence.
Source: equivalence unit and counit formulas
(blueprint: new-sf-canonical-ordinary-ringed-tensor-coherence). -/
def normalizedInverseHomComparison
    {A B : Type*} [Category A] [Category B] (E : B ≌ A)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HA) :
    HA ⋙ E.inverse ≅ E.inverse.op.prod E.inverse ⋙ HB := by
  let e : (E.inverse.op.prod E.inverse) ⋙ (E.functor.op.prod E.functor) ≅
      𝟭 (Aᵒᵖ × A) := NatIso.prod (NatIso.op E.counitIso.symm) E.counitIso
  exact (Functor.leftUnitor (HA ⋙ E.inverse)).symm ≪≫
    Functor.isoWhiskerRight e.symm (HA ⋙ E.inverse) ≪≫
    Functor.isoWhiskerLeft (E.inverse.op.prod E.inverse)
      (Functor.isoWhiskerRight h.symm E.inverse) ≪≫
    Functor.isoWhiskerLeft ((E.inverse.op.prod E.inverse) ⋙ HB) E.unitIso.symm ≪≫
    (Functor.rightUnitor _)

/-- The specified forward ordinary Hom comparison of a Frobenius model.
Source: the model's Hom naturality
(blueprint: new-sf-canonical-ordinary-ringed-tensor-coherence). -/
def frobeniusOrdinaryForwardHom
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X) :
    Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R)) ⋙ A.E.functor ≅
      A.E.functor.op.prod A.E.functor ⋙ Functor.uncurry.obj
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  NatIso.ofComponents (fun MN ↦ A.hom MN.1.unop MN.2)
    (fun fg ↦ A.hom_naturality fg.1.unop fg.2)

/-- Coherence with the actual fixed ordinary Hom maps of the model.
Source: Stacks 06YS, 06YU, 0FPT
(blueprint: new-sf-canonical-ordinary-ringed-tensor-coherence). -/
def FrobeniusOrdinaryTensorCoherence
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X) : Prop :=
  letI := A.additive
  letI : A.E.symm.functor.Additive := A.E.inverse_additive
  OrdinaryRingedTensorCoherence l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    A.J A.R A.E.symm (normalizedInverseHomComparison A.E
      (Functor.uncurry.obj
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
      (Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R)))
      (frobeniusOrdinaryForwardHom A))

/-- The canonical small-site forward Hom comparison.
Source: normalized adic section-module comparison
(blueprint: new-sf-canonical-ordinary-ringed-tensor-coherence). -/
def canonicalOrdinaryForwardHom (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :
    Functor.uncurry.obj (SheafOfModules.homFunctor (R := ProEtale.NativeFrobenius.ring Y l)) ⋙
        (ProEtale.NativeFrobenius.equivalence Y l).functor ≅
      (ProEtale.NativeFrobenius.equivalence Y l).functor.op.prod
        (ProEtale.NativeFrobenius.equivalence Y l).functor ⋙
        Functor.uncurry.obj (ordinaryIhomBifunctor l Y) :=
  NatIso.ofComponents (fun MN ↦ ProEtale.NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
    (fun fg ↦ ProEtale.NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2)

-- Forward associativity follows by cancelling the inverse comparison components.
private theorem forward_associativity_of_inverse
    {B A : Type*} [Category B] [Category A] [MonoidalCategory B] [MonoidalCategory A]
    (G : B ⥤ A)
    (τ : MonoidalCategory.tensor B ⋙ G ≅ G.prod G ⋙ MonoidalCategory.tensor A)
    (P Q N : B)
    (h : (τ.inv.app (P, Q) ▷ G.obj N) ≫ τ.inv.app (P ⊗ Q, N) ≫
        G.map (α_ P Q N).hom =
      (α_ (G.obj P) (G.obj Q) (G.obj N)).hom ≫
        (G.obj P ◁ τ.inv.app (Q, N)) ≫ τ.inv.app (P, Q ⊗ N)) :
    G.map (α_ P Q N).hom ≫ τ.hom.app (P, Q ⊗ N) ≫
        (G.obj P ◁ τ.hom.app (Q, N)) =
      τ.hom.app (P ⊗ Q, N) ≫ (τ.hom.app (P, Q) ▷ G.obj N) ≫
        (α_ (G.obj P) (G.obj Q) (G.obj N)).hom := by
  apply (cancel_epi ((τ.inv.app (P, Q) ▷ G.obj N) ≫ τ.inv.app (P ⊗ Q, N))).1
  simp only [Category.assoc]
  rw [reassoc_of% h]
  have hl : (G.obj P ◁ τ.inv.app (Q, N)) ≫ (G.obj P ◁ τ.hom.app (Q, N)) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id_app,
      MonoidalCategory.whiskerLeft_id]
  have hr : (τ.inv.app (P, Q) ▷ G.obj N) ≫ (τ.hom.app (P, Q) ▷ G.obj N) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.inv_hom_id_app, id_whiskerRight]
  simp only [Iso.inv_hom_id_app_assoc, reassoc_of% hr]
  erw [hl, Category.comp_id]

attribute [local irreducible] SheafOfModules.monoidalCategory Mod.monoidalCategoryStruct
attribute [local implicit_reducible] Mod.monoidalCategory Monoidal.induced

-- Lift and reverse associativity with abstract tensor instances before specializing them.
private theorem ordinary_chain_forward_associativity
    {B : Type*} [Category B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (F : B ⥤ A) [F.Additive]
    (ν : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (δ : MonoidalCategory.tensor (CochainComplex B ℤ) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        MonoidalCategory.tensor (CochainComplex A ℤ))
    (hδ : ∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (δ.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (hν : ∀ X Y Z : B,
      (ν.inv.app (X, Y) ▷ F.obj Z) ≫ ν.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          (F.obj X ◁ ν.inv.app (Y, Z)) ≫ ν.inv.app (X, Y ⊗ Z))
    (P Q N : CochainComplex B ℤ) :
    let G := F.mapHomologicalComplex (.up ℤ)
    G.map (α_ P Q N).hom ≫ δ.hom.app (P, Q ⊗ N) ≫
        (G.obj P ◁ δ.hom.app (Q, N)) =
      δ.hom.app (P ⊗ Q, N) ≫ (δ.hom.app (P, Q) ▷ G.obj N) ≫
        (α_ (G.obj P) (G.obj Q) (G.obj N)).hom := by
  exact forward_associativity_of_inverse (F.mapHomologicalComplex (.up ℤ)) δ P Q N
    (RingedForgetTensorTransposition.chain_inverse_associativity F ν δ hδ hν P Q N)


-- Compare the abstract native and ringed total-tensor instances through their APIs.
-- Specialize the chain coherence before constructing the signed ordinary comparison.
private theorem ordinary_chain_associativity_comparison
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (F : ProEtale.AdicSheaf l Y ⥤ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
    [F.Additive] :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∀ (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ F ≅
        F.prod F ⋙ MonoidalCategory.tensor _)
      (τ : MonoidalCategory.tensor (CochainComplex (ProEtale.AdicSheaf l Y) ℤ) ⋙
          F.mapHomologicalComplex (.up ℤ) ≅
        (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
          MonoidalCategory.tensor _),
      (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
        (p q n : ℤ) (h : p + q = n),
        F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (τ.hom.app (P, Q)).f n =
          ν.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιTensorObj
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h) →
      (∀ P Q N : ProEtale.AdicSheaf l Y,
        (ν.inv.app (P, Q) ▷ F.obj N) ≫ ν.inv.app (P ⊗ Q, N) ≫ F.map (α_ P Q N).hom =
          (α_ (F.obj P) (F.obj Q) (F.obj N)).hom ≫
            (F.obj P ◁ ν.inv.app (Q, N)) ≫ ν.inv.app (P, Q ⊗ N)) →
      ∀ P Q N : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
        let G := F.mapHomologicalComplex (.up ℤ)
        G.map (α_ P Q N).hom ≫ τ.hom.app (P, Q ⊗ N) ≫
            (G.obj P ◁ τ.hom.app (Q, N)) =
          τ.hom.app (P ⊗ Q, N) ≫ (τ.hom.app (P, Q) ▷ G.obj N) ≫
            (α_ (G.obj P) (G.obj Q) (G.obj N)).hom := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  intro ν τ ht ha P Q N
  exact ordinary_chain_forward_associativity F ν τ ht ha P Q N

private theorem ordinary_coherence_of_inverse_associativity
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u + 1})
    (E : ProEtale.AdicSheaf l Y ≌ RingedTensorModules.{u + 1, u + 1, u + 1} J R)
    [E.functor.Additive]
    (H : Functor.uncurry.obj (ordinaryIhomBifunctor l Y) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor (R := R))) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    (∀ (d : OrdinaryRingedTensorUnderivedData l Y J R E H)
      (b : ∀ P Q : ProEtale.AdicSheaf l Y,
        ((ordinaryTensorBifunctor l Y).obj P).obj Q ≅ Q ⊗ P)
      (ν : MonoidalCategory.tensor (ProEtale.AdicSheaf l Y) ⋙ E.functor ≅
        E.functor.prod E.functor ⋙ MonoidalCategory.tensor _),
      (∀ P Q, Mod.tensorπ Q P ≫ (b P Q).hom.hom = Mod.tensorObjπ Q P) →
      (∀ P Q, E.functor.map (b P Q).hom ≫ ν.hom.app (Q, P) =
        (d.underived P Q).hom) →
      ∀ P Q N : ProEtale.AdicSheaf l Y,
        (ν.inv.app (P, Q) ▷ E.functor.obj N) ≫ ν.inv.app (P ⊗ Q, N) ≫
            E.functor.map (α_ P Q N).hom =
          (α_ (E.functor.obj P) (E.functor.obj Q) (E.functor.obj N)).hom ≫
            (E.functor.obj P ◁ ν.inv.app (Q, N)) ≫ ν.inv.app (P, Q ⊗ N)) →
      ∀ (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
          ordinaryTensorTotal l Y P Q ≅ Q ⊗ P),
        (∀ (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
          (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
          Mod.tensorπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
                (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
            (p * q).negOnePow • (Mod.tensorObjπ (Q.X q) (P.X p) ≫
              (HomologicalComplex.ιTensorObj Q P q p n hqp).hom)) →
        ∀ d : OrdinaryRingedTensorUnderivedData l Y J R E H,
          Nonempty (OrdinaryRingedTensorChainComparison l Y J R E H κ d) := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  intro hassoc κ hκ d
  obtain ⟨b, hb⟩ := ordinary_relative_tensor_identification l Y
  obtain ⟨ν, τ, hd, ht⟩ := ordinary_ringed_tensor_termwise_comparison l Y J R E H d b hb
  have ha := hassoc d b ν hb hd
  refine ⟨{ tensor := τ, summand := ?_, associativity := ?_ }⟩
  · intro P Q p q n hpq hqp
    simp only [Units.smul_def]
    have hk :
        HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
            (.up ℤ) p q n hpq ≫ (κ P Q).hom.f n =
          ((p * q).negOnePow : ℤ) • ((b (P.X p) (Q.X q)).hom ≫
            HomologicalComplex.ιTensorObj Q P q p n hqp) := by
      apply Mod.tensorLeft_obj_hom_ext
      change Mod.tensorπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιMapBifunctor P Q (ordinaryTensorBifunctor l Y)
            (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
        Mod.tensorπ (Q.X q) (P.X p) ≫
          (((p * q).negOnePow : ℤ) • ((b (P.X p) (Q.X q)).hom.hom ≫
            (HomologicalComplex.ιTensorObj Q P q p n hqp).hom))
      simp only [Preadditive.comp_zsmul, ← Category.assoc, hb]
      simpa only [Units.smul_def, Category.assoc] using hκ P Q p q n hpq hqp
    rw [← E.functor.map_comp_assoc, hk, E.functor.map_zsmul,
      E.functor.map_comp,
      Preadditive.zsmul_comp, Category.assoc, ht, ← Category.assoc, hd]
    rfl
  · intro P Q N
    exact ordinary_chain_associativity_comparison l Y J R E.functor ν τ ht ha P Q N

attribute [local irreducible] ProEtale.NativeFrobenius.equivalence

/-- The canonical section-module equivalence retains its normalized tensor coherence.
Source: the pure-tensor and evaluation equations of the adic module comparison;
Stacks 03EO, 06YS, 06YU, 0FPT
(blueprint: new-sf-canonical-ordinary-ringed-tensor-coherence).

Proof: take the proved AdicModuleTensorComparisonCore on the pro-etale site.
Its tensor_sections equation gives associativity on triple pure tensors. The tensor quotient
universal property and the sheafification adjunction extend this equality to sheaf maps.
The evaluation formula for H identifies its Hom map with the mate of this exact tensorator.
Restrict to the small site, and reverse the equivalence using its unit and counit; this preserves
normalization and associativity. The uncurrying equation makes every supplied
underived d equal to this comparison. Totalize degreewise, exchange the two
parameters with (-1)^(pq), and use the balanced summand normalization of kappa.
The two triple signs agree by pq+(p+q)r=qr+p(q+r). Total coproduct inclusions
then prove associativity for unbounded complexes. This statement concerns the
canonical section equivalence and evaluation-normalized H, not an arbitrary Hom
isomorphism. No native tensor, native associator, or restriction bridge occurs. -/
theorem canonical_ordinary_ringed_tensor_coherence
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (H : ProEtale.AdicModuleHomComparisonCore l Y) :
    letI : (ProEtale.NativeFrobenius.equivalence Y l).symm.functor.Additive :=
      (ProEtale.NativeFrobenius.equivalence Y l).inverse_additive
    OrdinaryRingedTensorCoherence l Y (WeilFrobeniusAction.topology Y)
      (ProEtale.NativeFrobenius.ring Y l) (ProEtale.NativeFrobenius.equivalence Y l).symm
      (normalizedInverseHomComparison (ProEtale.NativeFrobenius.equivalence Y l)
        (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
        (Functor.uncurry.obj
          (SheafOfModules.homFunctor (R := ProEtale.NativeFrobenius.ring Y l)))
        (canonicalOrdinaryForwardHom l Y H)) := by
  let E := ProEtale.NativeFrobenius.equivalence Y l
  let _ : E.symm.functor.Additive := E.inverse_additive
  refine ⟨canonical_ordinary_tensor_symmetry l Y H, ?_⟩
  exact ordinary_coherence_of_inverse_associativity l Y (WeilFrobeniusAction.topology Y)
    (ProEtale.NativeFrobenius.ring Y l) E.symm
    (normalizedInverseHomComparison E
      (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
      (Functor.uncurry.obj
        (SheafOfModules.homFunctor (R := ProEtale.NativeFrobenius.ring Y l)))
      (canonicalOrdinaryForwardHom l Y H))
    (canonical_ordinary_tensor_inverse_associativity l Y H)

end AlgebraicGeometry.ProEtaleWeilSheaf
