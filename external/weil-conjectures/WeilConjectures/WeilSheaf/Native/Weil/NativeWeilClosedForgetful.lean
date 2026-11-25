/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorTransport
import WeilConjectures.WeilSheaf.Native.NativeClosedTransposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Forgetting Frobenius on native derived categories -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Forgetting Frobenius on the native derived category is exact, conservative,
commutes with cohomology, restricts to bounded constructible objects, and preserves
the closed symmetric derived tensor, evaluation, and transposed evaluation.

Source: prose-10-20, internal-Hom/evaluation/transposition;
native refinement in the eight-step DAG proof
(blueprint: lem-sf-weil-native-closed-forgetful).

Proof:
1. The semilinear geometric Frobenius is an automorphism. Close a small pro-etale
site under its integer iterates. Its action preserves the finite-subextension
continuous coefficient sheaf. The twisted action-site theorem identifies abelian
Weil sheaves with modules on that ringed site. Forgetting is its ringed pullback,
and has the exact orbit-sum induction as left adjoint.
2. Forgetting is exact on sheaves, hence induces the displayed triangulated
functor on unbounded derived categories. Exactness identifies cohomology with
underlying cohomology. Conservativity on sheaves and detection by all cohomology
objects imply conservativity on derived morphisms. Boundedness and constructibility
follow from that same comparison and the definition of WeilComplex.
3. Take K-flat flat-term and K-injective resolutions on the action site. Ringed
pullback preserves the former. The exact left adjoint makes forgetting preserve
the latter, by the right-adjoint K-injective criterion.
4. Apply the ringed derived closed symmetric monoidal theorem and its normalized
tensor--Hom adjunction. The Hom model agrees with the recorded two-K-injective
native derivedHom: precomposing with a source resolution is a quasi-isomorphism
by rhom-well-defined. This supplies the two-variable Hom models.
5. Forget total tensors of K-flat representatives. Both differentials are
 d_P tensor 1 + (-1)^p 1 tensor d_Q. Localize the identity on their summands;
derived tensor descent supplies its naturality. The Koszul symmetry is preserved.
6. Forget the product-total Hom between K-injective representatives. Products,
sheaf internal Hom, and their conjugation actions agree under forgetting, and the
underlying target stays K-injective. Resolution independence gives the ordinary
internal Hom comparison as an isomorphism of derived objects, natural in both
variables.
7. On simultaneous K-flat representatives the normalized adjunction uncurries
phi to x tensor y maps to phi(x)(y), followed by the inverse target augmentation.
Forgetting preserves this formula. Thus its derived Hom comparison is precisely
nativeHomComparison; its counit square is the displayed evaluation identity.
8. Transpose evaluation after symmetry using exactly that adjunction. Naturality
gives bidual_naturality. Steps 5--7 identify its ordinary uncurry after forgetting;
injectivity of the ordinary adjunction gives bidual_forget. No reflexivity is used.
-/
theorem native_closed_forgetful
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    (nativeForget k₀ l X).IsTriangulated ∧
    (nativeForget k₀ l X).ReflectsIsomorphisms ∧
    (∀ n : ℤ, Nonempty (nativeForget k₀ l X ⋙ DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))) ∧
    (∀ K : WeilComplex k₀ l X,
      DerivedCategory.TStructure.t.bounded ((nativeForget k₀ l X).obj K.obj) ∧
      ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
        ((DerivedCategory.homologyFunctor _ n).obj ((nativeForget k₀ l X).obj K.obj))) ∧
    (∃ C : NativeClosedComparison k₀ l X, C.Compatible) := by
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  refine ⟨inferInstance, ?_, (fun n ↦ ⟨(U.mapDerivedCategoryHomologyFunctorIso n).symm⟩),
    ?_, ?_⟩
  · constructor
    intro A B f hf
    have : IsIso (U.mapDerivedCategory.map f) := hf
    rw [DerivedCategory.isIso_iff]
    intro n
    have h : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ U).map f) :=
      (NatIso.isIso_map_iff (U.mapDerivedCategoryHomologyFunctorIso n) f).mpr
        (show IsIso ((DerivedCategory.homologyFunctor _ n).map
          (U.mapDerivedCategory.map f)) from inferInstance)
    have : IsIso (U.map ((DerivedCategory.homologyFunctor _ n).map f)) := h
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map f) U
  · intro K
    refine ⟨U.bounded_mapDerivedCategory_obj K.property.1, fun n ↦ ?_⟩
    exact (ProEtale.adicConstructibleSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).prop_of_iso
        ((U.mapDerivedCategoryHomologyFunctorIso n).app K.obj) (K.property.2 n)
  · obtain ⟨m⟩ := native_two_injective_hom_model (k₀ := k₀) (l := l) (X := X)
    obtain ⟨M, η, _, _, _, hrep⟩ := native_row_hom_comparison k₀ l X m
    obtain ⟨C, hM, hη, hcan, hcoh, hsym⟩ := native_tensor_transport k₀ l X M η hrep
    subst M
    have heq : C.homComparison = η := eq_of_heq hη
    subst η
    refine ⟨C, hcan, hrep, hcoh, hsym, ?_, ?_, ?_⟩
    · exact nativeComparison_evaluation _ _ _ _ _ hcan
    · exact nativeBidual_natural _ _
    · exact nativeComparison_bidual _ _ _ _ _ hcan _ _ hsym

end AlgebraicGeometry.ProEtaleWeilSheaf
