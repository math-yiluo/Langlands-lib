/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridge
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainData
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.BifunctorFlip

/-! # Two-sided K-flat representatives in the native derived category

Source: Stacks 06YS and 06YN. Transport ringed K-flat resolutions through the
native additive equivalence and test both tensor variables by mapping cones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem tests_of_acyclic
    {A : Type*} [Category* A] [Abelian A] [HasCountableCoproducts A]
    (F : A ⥤ A ⥤ A) [F.Additive] [∀ M, (F.obj M).Additive]
    (P : CochainComplex A ℤ)
    (h₁ : ∀ N : CochainComplex A ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor P N F).Acyclic)
    (h₂ : ∀ N : CochainComplex A ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P F).Acyclic) :
    (∀ {Q Q' : CochainComplex A ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.map₂CochainComplex.obj P).map f)) ∧
    (∀ {Q Q' : CochainComplex A ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.map₂CochainComplex.map f).app P)) := by
  constructor
  · intro Q Q' f hf
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    have hc := h₁ (CochainComplex.mappingCone f)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
    intro n
    exact (hc n).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso P f F)
  · intro Q Q' f hf
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
    have hc := h₂ (CochainComplex.mappingCone f)
      ((CochainComplex.mappingCone.quasiIso_iff_acyclic f).1 hf)
    intro n
    exact (hc n).of_iso (CochainComplex.mapBifunctorMappingCone₁Iso f P F)

private theorem acyclic_swap
    {A : Type*} [Category* A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A]
    [HasCountableCoproducts A]
    (P N : CochainComplex A ℤ)
    (h : (CochainComplex.mapBifunctor N P (curriedTensor A)).Acyclic) :
    (CochainComplex.mapBifunctor P N (curriedTensor A)).Acyclic := by
  let F := curriedTensor A
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj N).obj P) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj N).obj P) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ (N.X p) (P.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right (N.X p) (P.d q q')).symm))
      (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left (N.d p p') (P.X q)).symm)
  intro n
  exact (h n).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso P N F (.up ℤ))

private theorem flat_from_reversed_chain
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasCountableCoproducts A] [HasCountableCoproducts B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
    (F : A ⥤ A ⥤ A) [F.Additive] [∀ M, (F.obj M).Additive]
    [F.flip.Additive] [∀ M, (F.flip.obj M).Additive]
    (e₀ : A ≌ B) [e₀.functor.Additive]
    (chain : ∀ P N : CochainComplex A ℤ,
      (e₀.functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P N F) ≅
        (((curriedTensor B).map₂CochainComplex.obj
          ((e₀.functor.mapHomologicalComplex (.up ℤ)).obj N)).obj
          ((e₀.functor.mapHomologicalComplex (.up ℤ)).obj P)))
    (P : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (iP : (e₀.functor.mapHomologicalComplex (.up ℤ)).obj P ≅ L)
    (hL : ∀ N : CochainComplex B ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N L (curriedTensor B)).Acyclic) :
    (∀ {Q Q' : CochainComplex A ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.flip.map₂CochainComplex.obj P).map f)) ∧
    (∀ {Q Q' : CochainComplex A ℤ} (f : Q ⟶ Q'), QuasiIso f →
      QuasiIso ((F.flip.map₂CochainComplex.map f).app P)) := by
  let e := e₀.mapHomologicalComplex (.up ℤ)
  have hN (N : CochainComplex A ℤ) (hn : N.Acyclic) :
      (e.functor.obj N).Acyclic := hn.map e₀.functor
  have href (N : CochainComplex A ℤ)
      (hn : (e.functor.obj N).Acyclic) : N.Acyclic := by
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful (N.sc n) e₀.functor).mp (hn n)
  let tensor := Functor.uncurry.obj (curriedTensor B).map₂CochainComplex
  have hleft (N : CochainComplex A ℤ) (hn : N.Acyclic) :
      (CochainComplex.mapBifunctor P N F.flip).Acyclic := by
    let i := e.functor.mapIso (HomologicalComplex.mapBifunctorFlipIso N P F (.up ℤ)) ≪≫
      chain N P ≪≫ tensor.mapIso (iP.prod (Iso.refl (e.functor.obj N)))
    have ht := acyclic_swap L (e.functor.obj N) (hL _ (hN N hn))
    exact href _ (fun n ↦ (ht n).of_iso i.symm)
  have hright (N : CochainComplex A ℤ) (hn : N.Acyclic) :
      (CochainComplex.mapBifunctor N P F.flip).Acyclic := by
    let i := e.functor.mapIso (HomologicalComplex.mapBifunctorFlipIso P N F (.up ℤ)) ≪≫
      chain P N ≪≫ tensor.mapIso ((Iso.refl (e.functor.obj N)).prod iP)
    have ht := hL _ (hN N hn)
    exact href _ (fun n ↦ (ht n).of_iso i.symm)
  exact tests_of_acyclic F.flip P hleft hright

private def tensor_parametrized_adjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    nativeTensorBifunctor k₀ l X ⊣₂ ihomBifunctor k₀ l X :=
  { adj := tensorIhomAdjunction k₀ l X
    unit_whiskerRight_map := by
      intro A B f
      apply NatTrans.ext
      funext P
      exact (unit_conjugateEquiv_symm
        (tensorIhomAdjunction k₀ l X B) (tensorIhomAdjunction k₀ l X A)
        ((ihomBifunctor k₀ l X).map f.op) P).symm }

private instance tensor_additive
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    (nativeTensorBifunctor k₀ l X).Additive := by
  constructor
  intro A B f g
  apply NatTrans.ext
  funext N
  exact ((nativeTensorBifunctor k₀ l X).flip.obj N).map_add

private instance tensor_obj_additive
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (A : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).obj A).Additive :=
  (tensorIhomAdjunction k₀ l X A).left_adjoint_additive

attribute [local irreducible] nativeDerivedClosedComparison nativeTensorBifunctor

/-- Every native derived object has a representative satisfying both native K-flat tests.
Source: Stacks 06YS and 06YN
(blueprint: lem-sf-native-two-sided-kflat-representatives).

Proof: use the additive ringed presentation of the native module category. Resolve
the transported complex by a ringed K-flat complex and bring that resolution back
through the inverse complex equivalence. The counit identifies the transported
replacement with the chosen ringed K-flat complex. The native total-tensor comparison,
preceded by the signed interchange of the two total directions, identifies each
native tensor test with the ringed tensor test. Ringed symmetry gives the test in
the other variable. A quasi-isomorphism has acyclic mapping cone; the two tensor-cone
comparison isomorphisms therefore give preservation of quasi-isomorphisms in both
variables. Exact equivalences preserve and reflect the resolution quasi-isomorphism.
Localizing its augmentation and composing with a complex representative of the
derived object gives the required isomorphism. No fraction calculus on complexes
is assumed. -/
theorem native_two_sided_kflat_representatives
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : DerivedCategory (ProEtaleWeilSheaf k₀ l X)) :
    ∃ P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      NativeIsKFlat k₀ l X P ∧ Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  obtain ⟨b⟩ := native_weil_tensor_ringed_bridge k₀ l X
  let T := nativeTensorBifunctor k₀ l X
  let adj := tensor_parametrized_adjunction k₀ l X
  obtain ⟨v⟩ := native_weil_tensor_ringed_underived_data b T adj
  let sign (p q : ℤ) {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R}
      (f : Y ⟶ Z) : Y ⟶ Z :=
    letI : AddCommGroup (Y ⟶ Z) := Preadditive.homGroup Y Z
    ZSMul.zsmul ((p * q).negOnePow : ℤ) f
  obtain ⟨c⟩ := native_weil_tensor_ringed_chain_data b T adj v sign
    (fun _ _ _ _ _ ↦ rfl)
  let e := b.native.mapHomologicalComplex (.up ℤ)
  let K := DerivedCategory.Q.objPreimage M
  let := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  let := SheafOfModules.monoidalCategory b.R
  let := SheafOfModules.symmetricCategory b.R
  let := SheafOfModules.monoidalPreadditive_kfi b.R
  obtain ⟨L, q, hL, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (e.functor.obj K)
  let P := e.inverse.obj L
  let r : P ⟶ K := e.inverse.map q ≫ e.unitIso.inv.app K
  have hr : QuasiIso r := by
    have := hq
    have : QuasiIso (e.inverse.map q) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology q b.native.inverse
    dsimp only [r]
    infer_instance
  have hP : NativeIsKFlat k₀ l X P :=
    flat_from_reversed_chain T b.native c.chain P L (e.counitIso.app L) hL
  have := hr
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map r) ≪≫
    DerivedCategory.Q.objObjPreimageIso M⟩⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
