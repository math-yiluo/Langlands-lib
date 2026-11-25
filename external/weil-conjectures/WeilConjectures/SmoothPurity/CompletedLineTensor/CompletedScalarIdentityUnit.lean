/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The scalar identity unitor on all cochain representatives

Source: Stacks 06YY; blueprint Proof (3), ordinary identity normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.CompletedLineTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem line_model_functor :
    (WeilConjectures.completedScalarCochainModel l E E (AlgHom.id ℚ_[l] E) X).T =
      completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X := by
  rfl

private theorem line_model_complex :
    let M := WeilConjectures.completedScalarCochainModel l E E (AlgHom.id ℚ_[l] E) X
    M.E.mapHomologicalComplex (.up ℤ) =
      completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X := by
  rfl

private theorem line_model_counit (P : CochainComplex (integralTowerModules l E X) ℤ) :
    HEq ((WeilConjectures.completedScalarCochainModel l E E (AlgHom.id ℚ_[l] E) X).ε.app P)
      (completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P) := by
  exact heq_of_eq (completedScalarCochainModel_counit l E E (AlgHom.id ℚ_[l] E) X P)

attribute [local irreducible] WeilConjectures.completedScalarCochainModel

private theorem line_derived_unit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (D : DerivedCategory A ⥤ DerivedCategory A)
    (ε : DerivedCategory.Q ⋙ D ⟶ F ⋙ DerivedCategory.Q)
    (hd : D.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)))
    (μ : F ≅ 𝟭 (CochainComplex A ℤ)) :
    ∃ e : D ≅ 𝟭 (DerivedCategory A), ∀ P : CochainComplex A ℤ,
      e.hom.app (DerivedCategory.Q.obj P) =
        ε.app P ≫ DerivedCategory.Q.map (μ.hom.app P) := by
    let Q := DerivedCategory.Q (C := A)
    let j : F ⋙ Q ≅ Q := Functor.isoWhiskerRight μ Q ≪≫ Functor.leftUnitor Q
    have hi : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy (F ⋙ Q) :=
      (MorphismProperty.IsInvertedBy.iff_of_iso _ j).2 (Localization.inverts _ _)
    let := hd
    let := Functor.isIso_of_isLeftDerivedFunctor_of_inverts D ε hi
    let k : Q ⋙ D ≅ Q ⋙ 𝟭 _ := asIso ε ≪≫ j ≪≫ (Functor.rightUnitor Q).symm
    let ff := Localization.fullyFaithfulWhiskeringLeft Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory A)
    refine ⟨ff.preimageIso k, ?_⟩
    intro P
    have he := NatTrans.congr_app (ff.map_preimage k.hom) P
    change (ff.preimage k.hom).app (Q.obj P) = k.hom.app P at he
    change (ff.preimage k.hom).app (Q.obj P) = _
    rw [he]
    simp [k, j, Q]

private theorem line_unit_from_model
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F F' : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (D D' : DerivedCategory A ⥤ DerivedCategory A)
    (ε : DerivedCategory.Q ⋙ D ⟶ F ⋙ DerivedCategory.Q)
    (hd : D.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)))
    (hF : F = F') (hD : D = D') (μ : F' ≅ 𝟭 (CochainComplex A ℤ))
    (c : ∀ P : CochainComplex A ℤ,
      D'.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (F'.obj P))
    (hc : ∀ P, HEq (ε.app P) (c P)) :
    ∃ e : D' ≅ 𝟭 (DerivedCategory A), ∀ P : CochainComplex A ℤ,
      e.hom.app (DerivedCategory.Q.obj P) = c P ≫ DerivedCategory.Q.map (μ.hom.app P) := by
  subst F'
  subst D'
  obtain ⟨e, he⟩ := line_derived_unit F D ε hd μ
  refine ⟨e, ?_⟩
  intro P
  rw [he, eq_of_heq (hc P)]

/-- The derived identity scalar extension has its specified formula on every complex.
Source: Stacks 06YY; blueprint Proof (3)
(blueprint: lem-pur-ordinary-scalar-unit-all-complexes).
Proof: ordinary multiplication identifies the cochain extension with the identity.
Consequently it inverts quasi-isomorphisms after localization. The universal derived
counit is therefore invertible. Descend this counit followed by cochain multiplication
through the fully faithful localization whiskering functor. Its preimage is the
claimed isomorphism, and the preimage equation gives the formula on every complex.
The recorded cochain model and its counit identify these abstract maps with the
specified scalar extension and multiplication. -/
theorem ordinaryUnitOnComplexes_exists :
    ∃ e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) =
          completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P ≫
            DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  let M := WeilConjectures.completedScalarCochainModel l E E (AlgHom.id ℚ_[l] E) X
  exact line_unit_from_model
    (M.E.mapHomologicalComplex (.up ℤ))
    (completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X)
    M.T (completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X)
    M.ε M.universal (line_model_complex l E X) (line_model_functor l E X)
    (completedScalarIdentityMultiplication l E X)
    (completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X) (line_model_counit l E X)

end WeilConjectures.CompletedLineTensor
