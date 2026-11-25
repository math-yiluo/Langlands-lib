/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRestrictionTensor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import all WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import all WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived

/-! # The ordinary restriction tensorator on representatives

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-ordinary-restriction-total-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
-- Coherence compares the large localization and monoidal instance expressions.
private theorem exact_total_tensor_square
    {C : Type a} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type b} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] (P T : CochainComplex C ℤ) :
    letI := F.exactClosedDerivedMonoidal
    Functor.OplaxMonoidal.δ F.mapDerivedCategory (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj T) ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj T) =
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
      F.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
      DerivedCategory.Q.map (F.mapCochainComplexμIso P T).inv := by
  letI := F.exactClosedDerivedMonoidal
  letI := CategoryTheory.Functor.mapHomotopyMonoidal F
  haveI := CategoryTheory.Functor.derivedFactorsh_monoidal F
  haveI := CategoryTheory.Functor.mapHomotopyFactors_monoidal F
  haveI := CategoryTheory.ExactMonoidalEquivalenceDerived.quotientCompQh_monoidal (A := C)
  haveI := CategoryTheory.ExactMonoidalEquivalenceDerived.quotientCompQh_monoidal (A := D)
  let e := CategoryTheory.ExactMonoidalEquivalenceDerived.composeFactors
    (DerivedCategory.quotientCompQhIso C) (DerivedCategory.quotientCompQhIso D)
    (F.mapHomotopyCategoryFactors (.up ℤ)) F.mapDerivedCategoryFactorsh
  have he : e.hom = F.mapDerivedCategoryFactors.hom := by
    apply NatTrans.ext
    funext K
    rw [CategoryTheory.ExactMonoidalEquivalenceDerived.composeFactors_hom_app]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_app]
    exact Category.comp_id _
  haveI : NatTrans.IsMonoidal F.mapDerivedCategoryFactors.hom := by
    rw [← he]
    exact CategoryTheory.ExactMonoidalEquivalenceDerived.composeFactors_monoidal
      (DerivedCategory.quotientCompQhIso C) (DerivedCategory.quotientCompQhIso D)
      (F.mapHomotopyCategoryFactors (.up ℤ)) F.mapDerivedCategoryFactorsh
  have h := NatTrans.IsMonoidal.tensor (τ := F.mapDerivedCategoryFactors.hom) P T
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at h
  change (Functor.LaxMonoidal.μ F.mapDerivedCategory (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj T) ≫
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P T)) ≫
      F.mapDerivedCategoryFactors.hom.app (P ⊗ T) =
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app T) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj T) ≫
      DerivedCategory.Q.map (F.mapCochainComplexμIso P T).hom at h
  simp only [Category.assoc] at h
  apply (cancel_mono (DerivedCategory.Q.map (F.mapCochainComplexμIso P T).hom)).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [← h]
  erw [Category.comp_id]
  exact Functor.Monoidal.δ_μ_assoc F.mapDerivedCategory _ _ _

private theorem exact_total_tensor_square_transport
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M N P T L : C} {K P' T' W : D}
    (f : M ⟶ P) (g : N ⟶ T) (t : L ⟶ M ⊗ N)
    (i : K ≅ F.obj M ⊗ F.obj N)
    {a : F.obj P ⟶ P'} {b : F.obj T ⟶ T'} {μ : P' ⊗ T' ⟶ W}
    {q : F.obj (P ⊗ T) ⟶ W}
    (h : Functor.OplaxMonoidal.δ F P T ≫ (a ⊗ₘ b) ≫ μ = q) :
    (F.map t ≫ Functor.OplaxMonoidal.δ F M N ≫ i.inv) ≫ i.hom ≫
        ((F.map f ≫ a) ⊗ₘ (F.map g ≫ b)) ≫ μ =
      F.map t ≫ F.map (f ⊗ₘ g) ≫ q := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_assoc, h]

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The canonical balanced restriction isomorphism on ordinary total complexes.
Source: Stacks 012Z and 0E8I, totalization of the ordinary pullback tensorator.
(blueprint: lem-sf-native-ordinary-restriction-total-model). -/
def nativeOrdinaryRestrictionTotal
    (P T : CochainComplex (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ) :
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    (R.mapHomologicalComplex (.up ℤ)).obj (P ⊗ T) ≅
      (R.mapHomologicalComplex (.up ℤ)).obj P ⊗
        (R.mapHomologicalComplex (.up ℤ)).obj T := by
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let G := ProEtale.upperStar (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  letI : R.Monoidal := by
    dsimp only [R, ProEtale.adicUpperStar, Adjunction.modLeft]
    infer_instance
  letI : R.IsLeftAdjoint :=
    (ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j
        (Spec (CommRingCat.of k₀))))).isLeftAdjoint
  exact (R.mapCochainComplexμIso P T).symm

-- The native tensor comparisons contain large sheaf and derived-category instances.
/-- The fixed ordinary derived restriction tensorator is the localization of the
balanced total restriction map, including arbitrary input identification isomorphisms.

Source: Stacks 0E8I and 015F; the tensor/counit square of
`residueDerivedMonoidal_counit` transported to the exact derived functor.
(blueprint: lem-sf-native-ordinary-restriction-total-model).

Proof: install the braided pullback and its induced strong module tensor structure,
as in nativeOrdinaryRestrictionTensor. The ordinary total restriction is the inverse
complex tensorator for this very structure. Apply residueDerivedMonoidal_counit on
the images of P,T in the homotopy category. Substitute the canonical comparison
from the left derived functor to the exact derived functor. Its counit equation
identifies the substituted counit with mapDerivedCategoryFactors. The quotient to
the homotopy category is monoidal with identity tensorator; thus the formula is the
same for Q and nativeOrdinaryRestrictionTotal. Whisker by dZ.tensorIso and
(dU.tensorIso).symm; the latter cancels against dU.tensorIso. Finally use naturality
of the inverse derived tensorator along f and g and functoriality of tensor to move
the two input isomorphisms into the two factorization maps. This proves the formula
for arbitrary complexes, so zero complexes and unbounded diagonals require no
K-flat assumption. -/
theorem native_ordinary_restriction_total_model
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z)
    (P T : CochainComplex (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
    (M N : DerivedCategory (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (f : M ≅ DerivedCategory.Q.obj P) (g : N ≅ DerivedCategory.Q.obj T) :
    let R := ProEtale.adicUpperStar l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))));
    (nativeOrdinaryRestrictionTensor k₀ l j dU dZ).hom.app (M, N) ≫
      (dU.tensorIso k₀ l).hom.app (R.mapDerivedCategory.obj M, R.mapDerivedCategory.obj N) ≫
      (MonoidalCategory.tensor _).map
        (Prod.mkHom (R.mapDerivedCategory.map f.hom ≫ R.mapDerivedCategoryFactors.hom.app P)
          (R.mapDerivedCategory.map g.hom ≫ R.mapDerivedCategoryFactors.hom.app T)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((R.mapHomologicalComplex (.up ℤ)).obj P)
        ((R.mapHomologicalComplex (.up ℤ)).obj T) =
    R.mapDerivedCategory.map
      ((dZ.tensorIso k₀ l).hom.app (M, N) ≫
        (MonoidalCategory.tensor _).map (Prod.mkHom f.hom g.hom) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
      R.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
      DerivedCategory.Q.map (nativeOrdinaryRestrictionTotal k₀ l j P T).hom := by
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let G := ProEtale.upperStar (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  letI : R.Monoidal := by
    dsimp only [R, ProEtale.adicUpperStar, Adjunction.modLeft]
    infer_instance
  letI : R.PreservesFlat := native_adic_restriction_flat l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  letI : R.IsLeftAdjoint :=
    (ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j
        (Spec (CommRingCat.of k₀))))).isLeftAdjoint
  letI := R.exactClosedDerivedMonoidal
  have h := exact_total_tensor_square R P T
  have hfinal := exact_total_tensor_square_transport R.mapDerivedCategory f.hom g.hom
    ((dZ.tensorIso k₀ l).hom.app (M, N))
    ((dU.tensorIso k₀ l).app (R.mapDerivedCategory.obj M, R.mapDerivedCategory.obj N))
    h
  change (R.mapDerivedCategory.map ((dZ.tensorIso k₀ l).hom.app (M, N)) ≫
      Functor.OplaxMonoidal.δ R.mapDerivedCategory M N ≫
      (dU.tensorIso k₀ l).inv.app (R.mapDerivedCategory.obj M,
        R.mapDerivedCategory.obj N)) ≫
      (dU.tensorIso k₀ l).hom.app (R.mapDerivedCategory.obj M, R.mapDerivedCategory.obj N) ≫
      (MonoidalCategory.tensor _).map
        (Prod.mkHom (R.mapDerivedCategory.map f.hom ≫ R.mapDerivedCategoryFactors.hom.app P)
          (R.mapDerivedCategory.map g.hom ≫ R.mapDerivedCategoryFactors.hom.app T)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((R.mapHomologicalComplex (.up ℤ)).obj P)
        ((R.mapHomologicalComplex (.up ℤ)).obj T) = _
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  change R.mapDerivedCategory.map ((dZ.tensorIso k₀ l).hom.app (M, N)) ≫
      Functor.OplaxMonoidal.δ R.mapDerivedCategory M N ≫
      ((R.mapDerivedCategory.map f.hom ≫ R.mapDerivedCategoryFactors.hom.app P) ⊗ₘ
        (R.mapDerivedCategory.map g.hom ≫ R.mapDerivedCategoryFactors.hom.app T)) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((R.mapHomologicalComplex (.up ℤ)).obj P)
        ((R.mapHomologicalComplex (.up ℤ)).obj T) =
    R.mapDerivedCategory.map
      ((dZ.tensorIso k₀ l).hom.app (M, N) ≫ (f.hom ⊗ₘ g.hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P T) ≫
      R.mapDerivedCategoryFactors.hom.app (P ⊗ T) ≫
      DerivedCategory.Q.map (R.mapCochainComplexμIso P T).inv
  simpa only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv,
    Iso.inv_hom_id_app_assoc] using hfinal

end AlgebraicGeometry.ProEtaleWeilSheaf
