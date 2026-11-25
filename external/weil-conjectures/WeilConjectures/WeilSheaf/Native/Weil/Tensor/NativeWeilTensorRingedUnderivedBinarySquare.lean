/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorUnderivedData
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetChainUncurry
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # The binary square for normalized native tensor complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open CategoryTheory.BraidedCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

section SiteMates

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem tensorHomEquiv_eq (P Q I : RingedTensorModules.{u, u, u} J R) :
    SheafOfModules.tensorHomEquiv (R := R) P Q I =
      ZeroClassAux.tensorHomEquiv.{u, u, u} R P Q I := by
  apply Equiv.ext
  intro f
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  apply PresheafOfModules.hom_ext
  intro W
  refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  rfl

private def binaryMate (P Q I : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) : Q ⊗ P ⟶ I :=
  (β_ Q P).hom ≫ ((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f

private theorem binaryMate_eq (P Q I : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P Q I f = (f ⊗ₘ 𝟙 P) ≫
      RingedForgetTensorTransposition.ordinaryEvaluation J R P I := by
  have he : ((SheafOfModules.tensorHomAdjunction R P).homEquiv
      (SheafOfModules.homObj (R := R) P I) I).symm (𝟙 _) =
    (ZeroClassAux.tensorHomEquiv.{u, u, u} R P
      (SheafOfModules.homObj (R := R) P I) I).symm (𝟙 _) := by
    simp only [SheafOfModules.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
      tensorHomEquiv_eq]
    rfl
  have hn := (SheafOfModules.tensorHomAdjunction R P).homEquiv_naturality_left_symm
    f (𝟙 (SheafOfModules.homObj (R := R) P I))
  simp only [Category.comp_id] at hn
  rw [binaryMate, hn, he]
  dsimp only [RingedForgetTensorTransposition.ordinaryEvaluation]
  change (β_ Q P).hom ≫ (P ◁ f) ≫ _ = _
  rw [← id_tensorHom, ← braiding_naturality_assoc]

private theorem binaryMate_pre (P Q Q' I : RingedTensorModules.{u, u, u} J R)
    (a : Q' ⟶ Q) (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P Q' I (a ≫ f) = (a ⊗ₘ 𝟙 P) ≫ binaryMate R P Q I f := by
  simp only [binaryMate_eq, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

set_option linter.unusedSectionVars false in
private theorem binaryMate_post (P Q I I' : RingedTensorModules.{u, u, u} J R)
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I) (a : I ⟶ I') :
    binaryMate R P Q I' (f ≫ SheafOfModules.homObjMap (R := R) (𝟙 P) a) =
      binaryMate R P Q I f ≫ a := by
  dsimp only [binaryMate]
  rw [Category.assoc]
  congr 1
  exact (SheafOfModules.tensorHomAdjunction R P).homEquiv_naturality_right_symm f a

set_option linter.unusedSectionVars false in
private theorem binaryMate_change (P P' Q I : RingedTensorModules.{u, u, u} J R)
    (a : P' ⟶ P) (f : Q ⟶ SheafOfModules.homObj (R := R) P I) :
    binaryMate R P' Q I (f ≫ SheafOfModules.homObjMap (R := R) a (𝟙 I)) =
      (𝟙 Q ⊗ₘ a) ≫ binaryMate R P Q I f := by
  dsimp only [binaryMate]
  have hn : ((SheafOfModules.tensorHomAdjunction R P').homEquiv Q I).symm
      (f ≫ SheafOfModules.homObjMap (R := R) a (𝟙 I)) =
      (a ▷ Q) ≫ ((SheafOfModules.tensorHomAdjunction R P).homEquiv Q I).symm f := by
    simp only [SheafOfModules.tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
    apply (SheafOfModules.tensorHomEquiv (R := R) P' Q I).injective
    erw [Equiv.apply_symm_apply,
      SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := R),
      Equiv.apply_symm_apply]
  rw [hn, ← Category.assoc, ← tensorHom_id, ← braiding_naturality]
  simp only [Category.assoc]

private theorem binaryMate_iso (P P' Q Q' I I' : RingedTensorModules.{u, u, u} J R)
    (a : P ≅ P') (b : Q ⟶ Q') (c : I ⟶ I')
    (f : Q ⟶ SheafOfModules.homObj (R := R) P I)
    (g : Q' ⟶ SheafOfModules.homObj (R := R) P' I')
    (h : f ≫ SheafOfModules.homObjMap (R := R) a.inv c = b ≫ g) :
    binaryMate R P Q I f ≫ c = (b ⊗ₘ a.hom) ≫ binaryMate R P' Q' I' g := by
  apply (cancel_epi (𝟙 Q ⊗ₘ a.inv)).1
  rw [← binaryMate_post]
  have hm : SheafOfModules.homObjMap (R := R) (𝟙 P) c ≫
      SheafOfModules.homObjMap (R := R) a.inv (𝟙 I') =
      SheafOfModules.homObjMap (R := R) a.inv c := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id]
  rw [← binaryMate_change, Category.assoc, hm, h, binaryMate_pre]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    a.inv_hom_id]

end SiteMates

-- Perform the final cancellation before specializing to concrete sheaf functors.
private theorem binary_square_of_inverse {C : Type*} [Category C]
    {A B E F G H : C} (a : A ≅ B) (b : E ≅ F) (c : G ≅ E)
    (s : A ⟶ G) (t : B ⟶ H) (r : H ⟶ F)
    (h : t ≫ r ≫ b.inv ≫ c.inv = a.inv ≫ s) :
    a.hom ≫ t ≫ r = s ≫ c.hom ≫ b.hom := by
  apply (cancel_epi a.inv).1
  apply (cancel_mono b.inv).1
  apply (cancel_mono c.inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h

attribute [local irreducible] SheafOfModules.monoidalCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X}
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (D : NativeWeilTensorRingedAssociatorChainData k₀ l X T)

-- Compare the two concrete sheaf tensor constructions in the evaluation square.
private theorem binaryMate_forget
    (P Q I : RingedTensorModules.{u + 1, u + 1, u + 1} D.b.J D.b.R)
    (f : Q ⟶ SheafOfModules.homObj (R := D.b.R) P I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
    letI := SheafOfModules.monoidalCategory D.b.R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
    letI := SheafOfModules.monoidalCategory D.b.Q
    D.b.underived.tensor.hom.app (Q, P) ≫
        binaryMate D.b.Q (D.b.forget.obj P) (D.b.forget.obj Q) (D.b.forget.obj I)
          (D.b.forget.map f ≫ D.b.underived.hom.hom.app (op P, I)) =
      D.b.forget.map (binaryMate D.b.R P Q I f) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  let := SheafOfModules.monoidalCategory D.b.R
  let := SheafOfModules.symmetricCategory D.b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
  let := SheafOfModules.monoidalCategory D.b.Q
  let := SheafOfModules.symmetricCategory D.b.Q
  have he := D.b.underived.evaluation P I
    (RingedForgetTensorTransposition.ordinaryEvaluation.{u + 1, u + 1, u + 1} D.b.J D.b.R P I)
    (RingedForgetTensorTransposition.ordinaryEvaluation.{u + 1, u + 1, u + 1} D.b.K D.b.Q
      (D.b.forget.obj P) (D.b.forget.obj I))
    (RingedForgetTensorTransposition.ordinaryEvaluation_pure.{u + 1, u + 1, u + 1} D.b.J D.b.R P I)
    (RingedForgetTensorTransposition.ordinaryEvaluation_pure.{u + 1, u + 1, u + 1} D.b.K D.b.Q
      (D.b.forget.obj P) (D.b.forget.obj I))
  have hn := D.b.underived.tensor.hom.naturality
    (X := (Q, P)) (Y := (SheafOfModules.homObj (R := D.b.R) P I, P)) (f, 𝟙 P)
  change D.b.forget.map (f ⊗ₘ 𝟙 P) ≫ D.b.underived.tensor.hom.app (_, P) =
    D.b.underived.tensor.hom.app (Q, P) ≫
      (D.b.forget.map f ⊗ₘ D.b.forget.map (𝟙 P)) at hn
  simp only [CategoryTheory.Functor.map_id] at hn
  change D.b.underived.tensor.hom.app (_, P) ≫
      (D.b.underived.hom.hom.app (op P, I) ⊗ₘ 𝟙 (D.b.forget.obj P)) ≫ _ = _ at he
  rw [binaryMate_eq, binaryMate_eq, Functor.map_comp]
  have hc : ((D.b.forget.map f ≫ D.b.underived.hom.hom.app (op P, I)) ⊗ₘ
      𝟙 (D.b.forget.obj P)) =
      (D.b.forget.map f ⊗ₘ 𝟙 (D.b.forget.obj P)) ≫
        (D.b.underived.hom.hom.app (op P, I) ⊗ₘ 𝟙 (D.b.forget.obj P)) := by
    simpa only [Category.comp_id] using (tensorHom_comp_tensorHom
      (D.b.forget.map f) (𝟙 (D.b.forget.obj P))
      (D.b.underived.hom.hom.app (op P, I)) (𝟙 (D.b.forget.obj P))).symm
  rw [hc, Category.assoc, ← reassoc_of% hn]
  exact congrArg (D.b.forget.map (f ⊗ₘ 𝟙 P) ≫ ·) he

-- Compare the two site tensor instances through the bridge.
-- The normalized mates involve both concrete tensor constructions.
/-- The two evaluation-normalized underived tensor comparisons form a binary square.
Source: Stacks 06YS and 06YU
(blueprint: new-sf-native-weil-tensor-ringed-underived-binary-square).

Proof: invert all tensor comparisons and apply the ordinary tensor--Hom
adjunction. Substitute the native uncurrying equation, `he`, and the ordinary
uncurrying equation. Naturality of the bridge square moves the adjunct across
its component. Its Hom square identifies the two remaining Hom maps. The
restriction evaluation equation identifies the mate of its tensorator, and
its symmetry equation cancels the braidings introduced by reversing the tensor
parameter. Injectivity of the adjunction and cancellation of the isomorphisms
give the displayed square. There are only two underived factors here; no
complexes, signs, or associator calculations occur. -/
theorem native_weil_tensor_ringed_underived_binary_square
    (d : NativeOrdinaryRingedTensorUnderivedData D.b)
    (P Q : ProEtaleWeilSheaf k₀ l X) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
    letI := SheafOfModules.monoidalCategory D.b.R
    letI := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
    letI := SheafOfModules.monoidalCategory D.b.Q
    D.b.forget.map (D.A.underived P Q).hom ≫
        D.b.underived.tensor.hom.app (D.b.native.functor.obj Q,
          D.b.native.functor.obj P) ≫
        (D.b.square.hom.app Q ⊗ₘ D.b.square.hom.app P) =
      D.b.square.hom.app ((T.obj P).obj Q) ≫
        D.b.ordinary.functor.map (D.e.hom.app (P, Q)) ≫
        (d.underived P.carrier Q.carrier).hom := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.R
  let := SheafOfModules.monoidalCategory D.b.R
  let := SheafOfModules.symmetricCategory D.b.R
  let := SheafOfModules.isMonoidal_W_independentCoefficients D.b.Q
  let := SheafOfModules.monoidalCategory D.b.Q
  let := SheafOfModules.symmetricCategory D.b.Q
  let I := (T.obj P).obj Q
  let f := (D.adj.adj P).homEquiv Q I (𝟙 I)
  have hf : ((D.adj.adj P).homEquiv Q I).symm f = 𝟙 I :=
    (D.adj.adj P).homEquiv Q I |>.symm_apply_apply (𝟙 I)
  have ha := D.A.uncurry P Q I f
  rw [hf, CategoryTheory.Functor.map_id, Category.comp_id] at ha
  change (D.A.underived P Q).inv =
    binaryMate D.b.R (D.b.native.functor.obj P) (D.b.native.functor.obj Q)
      (D.b.native.functor.obj I) (D.b.native.functor.map f ≫
      D.b.nativeHom.hom.app (op P, I)) at ha
  have ho := d.uncurry P.carrier Q.carrier I.carrier f.hom.f
  have hh := D.he P Q I f
  rw [hf] at hh
  change D.e.inv.app (P, Q) ≫ 𝟙 _ = _ at hh
  rw [Category.comp_id] at hh
  rw [← hh] at ho
  change (d.underived P.carrier Q.carrier).inv ≫
      D.b.ordinary.functor.map (D.e.inv.app (P, Q)) =
    binaryMate D.b.Q (D.b.ordinary.functor.obj P.carrier)
      (D.b.ordinary.functor.obj Q.carrier) (D.b.ordinary.functor.obj I.carrier)
      (D.b.ordinary.functor.map f.hom.f ≫
      D.b.ordinaryHom.hom.app (op P.carrier, I.carrier)) at ho
  have hs := D.b.hom_square P I
  have hs' := congrArg (· ≫ D.b.ordinaryHom.hom.app (op P.carrier, I.carrier)) hs
  simp only [Category.assoc, Iso.inv_hom_id_app] at hs'
  have hn := D.b.square.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have hm : (D.b.forget.map (D.b.native.functor.map f ≫
      D.b.nativeHom.hom.app (op P, I)) ≫
      D.b.underived.hom.hom.app (op (D.b.native.functor.obj P),
        D.b.native.functor.obj I)) ≫
      SheafOfModules.homObjMap (R := D.b.Q) (D.b.square.inv.app P)
        (D.b.square.hom.app I) =
    D.b.square.hom.app Q ≫ (D.b.ordinary.functor.map f.hom.f ≫
      D.b.ordinaryHom.hom.app (op P.carrier, I.carrier)) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [hs', ← Category.assoc, hn]
    rfl
  have hb := binaryMate_iso D.b.Q _ _ _ _ _ _ (D.b.square.app P)
    (D.b.square.hom.app Q) (D.b.square.hom.app I) _ _ hm
  erw [← ho] at hb
  have ht := binaryMate_forget D (D.b.native.functor.obj P)
    (D.b.native.functor.obj Q) (D.b.native.functor.obj I) (D.b.native.functor.map f ≫
    D.b.nativeHom.hom.app (op P, I))
  erw [← ha] at ht
  have hv := congrArg (D.b.underived.tensor.hom.app
    (D.b.native.functor.obj Q, D.b.native.functor.obj P) ≫ ·) hb
  erw [← Category.assoc, ht] at hv
  exact binary_square_of_inverse (D.b.forget.mapIso (D.A.underived P Q))
    (d.underived P.carrier Q.carrier) (D.b.ordinary.functor.mapIso (D.e.app (P, Q)))
    (D.b.square.hom.app I) _ _ hv.symm

end AlgebraicGeometry.ProEtaleWeilSheaf
