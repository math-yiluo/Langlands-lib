/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperationModels
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralSystemProperOpenTransport
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemTensorComposition

/-! # Canonical integral model construction steps

Source: blueprint fix-prop-coherence, strict-system realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem tensorComparison_congr {C D : Type*} [Category C] [Category D]
    {I : Type*} (T : C × C ⥤ C) (S : D × D ⥤ D) (F : I → C ⥤ D)
    (μ : ∀ f A B, (F f).obj (T.obj (A, B)) ⟶ S.obj ((F f).obj A, (F f).obj B))
    {f g : I} (h : f = g) (A B : C) :
    (eqToIso (congrArg F h)).hom.app (T.obj (A, B)) ≫ μ g A B =
      μ f A B ≫ S.map
        (Prod.mkHom ((eqToIso (congrArg F h)).hom.app A)
          ((eqToIso (congrArg F h)).hom.app B)) := by
  subst g
  simp

private theorem tensorComparison_square {D : Type*} [Category D]
    (S : D × D ⥤ D) {A₀ B₀ T₀ A₁ B₁ T₁ A₂ B₂ T₂ A₃ B₃ T₃ N : D}
    (aT : T₀ ⟶ T₂) (aA : A₀ ⟶ A₂) (aB : B₀ ⟶ B₂)
    (bT : T₁ ⟶ T₃) [Epi bT] (bTi : T₃ ⟶ T₁)
    (bA : A₁ ⟶ A₃) (bAi : A₃ ⟶ A₁) (bB : B₁ ⟶ B₃) (bBi : B₃ ⟶ B₁)
    (eT : T₁ ⟶ T₀) (eA : A₁ ⟶ A₀) (eB : B₁ ⟶ B₀)
    (sT : T₃ ⟶ T₂) (sA : A₃ ⟶ A₂) (sB : B₃ ⟶ B₂)
    (hsT : sT = bTi ≫ eT ≫ aT) (hsA : sA = bAi ≫ eA ≫ aA)
    (hsB : sB = bBi ≫ eB ≫ aB)
    (hT : bT ≫ bTi = 𝟙 T₁) (hA : bA ≫ bAi = 𝟙 A₁)
    (hB : bB ≫ bBi = 𝟙 B₁)
    (μ : T₂ ⟶ S.obj (A₂, B₂)) (ν₁ : T₃ ⟶ N) (ν₂ : N ⟶ S.obj (A₃, B₃))
    (φ : T₀ ⟶ S.obj (A₀, B₀)) (ψ : T₁ ⟶ S.obj (A₁, B₁))
    (ha : aT ≫ μ = φ ≫ S.map (Prod.mkHom aA aB))
    (hb : bT ≫ ν₁ ≫ ν₂ = ψ ≫ S.map (Prod.mkHom bA bB))
    (he : eT ≫ φ = ψ ≫ S.map (Prod.mkHom eA eB)) :
    sT ≫ μ = ν₁ ≫ ν₂ ≫ S.map (Prod.mkHom sA sB) := by
  rw [hsT, hsA, hsB]
  apply (cancel_epi bT).mp
  simp only [Category.assoc, reassoc_of% hT]
  rw [ha, reassoc_of% hb, ← Category.assoc, he]
  simp only [Category.assoc, ← Functor.map_comp, prod_comp,
    reassoc_of% hA, reassoc_of% hB]

private theorem trans_hom_app {C D : Type*} [Category C] [Category D]
    {F G P R : C ⥤ D} (a : G ≅ R) (e : G ≅ F) (b : F ≅ P) (A : C) :
    (a.symm ≪≫ e ≪≫ b).hom.app A = a.inv.app A ≫ e.hom.app A ≫ b.hom.app A := by
  rfl

attribute [local irreducible] pullbackTensorCalculus pullbackTensorSystemComparison
  pullbackTensorSequenceDerived Functor.mapDerivedCategory CoefficientClosedStructure.tensor
  HasDerivedCategory.standard coefficientSequenceInternalHom

private theorem systemTensorCongr {X Z : Scheme.{u}} {f g : X ⟶ Z}
    (h : f = g) (A B : System l E Z) :
    (eqToIso (congrArg (pull l E) h)).hom.app
        ((calculus l E Z).systemClosed.tensor.obj (A, B)) ≫
      (pullbackTensorSystemComparison l E g).hom.app (A, B) =
    (pullbackTensorSystemComparison l E f).hom.app (A, B) ≫
      (calculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((eqToIso (congrArg (pull l E) h)).hom.app A)
          ((eqToIso (congrArg (pull l E) h)).hom.app B)) := by
  exact tensorComparison_congr
    (calculus l E Z).systemClosed.tensor (calculus l E X).systemClosed.tensor
    (pull l E) (fun f A B ↦ (pullbackTensorSystemComparison l E f).hom.app (A, B)) h A B

-- First identify the isomorphism, then take components of that equality.
private theorem square_eq (o : Operations l E) (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    c.square l E k r p i h =
      (c.pullComp r i).symm ≪≫ eqToIso (congrArg (pull l E) h.symm) ≪≫ c.pullComp k p := by
  rfl

private theorem square_hom_app (o : Operations l E) (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) (A : System l E Z) :
    (c.square l E k r p i h).hom.app A =
      (c.pullComp r i).inv.app A ≫ (eqToIso (congrArg (pull l E) h.symm)).hom.app A ≫
        (c.pullComp k p).hom.app A := by
  exact (congrArg
    (fun e : pull l E i ⋙ pull l E r ≅ pull l E p ⋙ pull l E k ↦ e.hom.app A)
    (square_eq l E o c k r p i h)).trans
      (trans_hom_app (c.pullComp r i) (eqToIso (congrArg (pull l E) h.symm))
        (c.pullComp k p) A)

private theorem systemTensorSquare (o : Operations l E) (c : Compositors l E o) :
    ∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (h : k ≫ p = r ≫ i) (A B : System l E Z),
        (c.square l E k r p i h).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)) ≫
            (pull l E k).map ((pullbackTensorSystemComparison l E p).hom.app (A, B)) ≫
            (pullbackTensorSystemComparison l E k).hom.app
              ((pull l E p).obj A, (pull l E p).obj B) =
          (pull l E r).map ((pullbackTensorSystemComparison l E i).hom.app (A, B)) ≫
            (pullbackTensorSystemComparison l E r).hom.app
              ((pull l E i).obj A, (pull l E i).obj B) ≫
            (calculus l E U).systemClosed.tensor.map
              (Prod.mkHom ((c.square l E k r p i h).hom.app A)
                ((c.square l E k r p i h).hom.app B)) := by
  intro U V W Z k r p i h A B
  exact tensorComparison_square (calculus l E U).systemClosed.tensor
    ((c.pullComp k p).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)))
    ((c.pullComp k p).hom.app A) ((c.pullComp k p).hom.app B)
    ((c.pullComp r i).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)))
    ((c.pullComp r i).inv.app ((calculus l E Z).systemClosed.tensor.obj (A, B)))
    ((c.pullComp r i).hom.app A) ((c.pullComp r i).inv.app A)
    ((c.pullComp r i).hom.app B) ((c.pullComp r i).inv.app B)
    ((eqToIso (congrArg (pull l E) h.symm)).hom.app
      ((calculus l E Z).systemClosed.tensor.obj (A, B)))
    ((eqToIso (congrArg (pull l E) h.symm)).hom.app A)
    ((eqToIso (congrArg (pull l E) h.symm)).hom.app B)
    ((c.square l E k r p i h).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)))
    ((c.square l E k r p i h).hom.app A) ((c.square l E k r p i h).hom.app B)
    (square_hom_app l E o c k r p i h _)
    (square_hom_app l E o c k r p i h A) (square_hom_app l E o c k r p i h B)
    (Iso.hom_inv_id_app (c.pullComp r i) _)
    (Iso.hom_inv_id_app (c.pullComp r i) A) (Iso.hom_inv_id_app (c.pullComp r i) B)
    ((pull l E k).map ((pullbackTensorSystemComparison l E p).hom.app (A, B)) ≫
      (pullbackTensorSystemComparison l E k).hom.app
        ((pull l E p).obj A, (pull l E p).obj B))
    ((pull l E r).map ((pullbackTensorSystemComparison l E i).hom.app (A, B)))
    ((pullbackTensorSystemComparison l E r).hom.app
      ((pull l E i).obj A, (pull l E i).obj B))
    ((pullbackTensorSystemComparison l E (k ≫ p)).hom.app (A, B))
    ((pullbackTensorSystemComparison l E (r ≫ i)).hom.app (A, B))
    (integralSystemTensorComposition l E o c k p A B)
    (integralSystemTensorComposition l E o c r i A B)
    (systemTensorCongr l E h.symm A B)

/-- Canonical system operations and their left-adjoint tensor square. This statement
contains no reduction/limit realization or completed ringed models.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI, 0941, 07A7, 0F7B--0F7F;
blueprint fix-prop-coherence, strict-system realization steps 1--2
(blueprint: lem-sf-integral-canonical-system-coherence).

Proof: derive the ordinary sequence-site direct image by K-injective resolution,
retaining its universal derived comparison and the adjunction transpose on complexes.
Exact inverse image has its specified factorization. Finite left extension to level
n is left adjoint to evaluation, so adjunction and Yoneda give direct evaluation;
transposing the fixed inverse evaluation fixes both adjunction identities. Naturality
in the quotient ring maps gives restrictedDirect and its transition equation. For an
open immersion use exact extension by zero on the sequence site; its adjunction to
inverse image gives Open and its evaluated inverse mate. This constructs Operations.
Compose ordinary direct images by pullback of sections along pullbackComp. Transpose
that section map to obtain ordinaryPull, then localize on complexes for pullComp and
its representative equation. The ordinary direct image is also the identity-section
presentation of the intrinsic semilinear direct image, giving CanonicalBridge.
The open-unit isomorphism, open base change, projection and clopen identification
are the exact slice adjunction comparisons; take their displayed transposes to fix
OpenComparisons. Transport intrinsic semilinear gamma along the bridge. Adjunction
transport identifies its transpose with properOpenLambda; the intrinsic vertical,
horizontal and base-change equations give ProperOpenCoherence. Finally the two
inverse-image tensor comparisons around any commutative square agree: on flat-term
K-flat complexes each takes a generalized pure tensor to the same pair of pulled
back sections. The ordinary section compositor supplies the square identification.
Tensor generation proves equality on each total summand, and localization gives the
following equality before any right-adjoint mate or finite evaluation is taken. -/
theorem integralCanonicalSystemCoherence :
    ∃ (o : Operations l E) (c : Compositors l E o)
      (a : OpenComparisons l E o c) (b : CanonicalBridge l E o),
      Nonempty (ProperOpenCoherence l E o c a b) ∧
      ∀ {U V W Z : Scheme.{u}}
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (h : k ≫ p = r ≫ i) (A B : System l E Z),
        (c.square l E k r p i h).hom.app ((calculus l E Z).systemClosed.tensor.obj (A, B)) ≫
            (pull l E k).map ((pullbackTensorSystemComparison l E p).hom.app (A, B)) ≫
            (pullbackTensorSystemComparison l E k).hom.app
              ((pull l E p).obj A, (pull l E p).obj B) =
          (pull l E r).map ((pullbackTensorSystemComparison l E i).hom.app (A, B)) ≫
            (pullbackTensorSystemComparison l E r).hom.app
              ((pull l E i).obj A, (pull l E i).obj B) ≫
            (calculus l E U).systemClosed.tensor.map
              (Prod.mkHom ((c.square l E k r p i h).hom.app A)
                ((c.square l E k r p i h).hom.app B)) := by
  obtain ⟨o, c, ⟨a⟩, ⟨b⟩⟩ := integralSystemOperationModels l E
  refine ⟨o, c, a, b, integralSystemProperOpenTransport l E o c a b, ?_⟩
  intro U V W Z k r p i h A B
  exact systemTensorSquare l E o c k r p i h A B

end WeilConjectures.IntegralSystemRealization
