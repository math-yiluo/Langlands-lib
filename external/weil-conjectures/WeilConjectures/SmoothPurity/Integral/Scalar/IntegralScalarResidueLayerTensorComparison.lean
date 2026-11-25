/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueCoefficientIso
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The balanced tensor comparison for a uniformizer layer

Source: the first two sentences of the residue-layer argument of
lem-sf-integral-scalar-residue-layer-constructible; Stacks, Modules on Sites,
Tag 03EK, and Mathlib's Ideal.quotEquivPowQuotPowSucc.
(blueprint: lem-sf-integral-scalar-residue-layer-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
namespace WeilConjectures

section TensorComparison

variable (Y : AlgebraicGeometry.Scheme.{u})

private instance residueSiteSmall : EssentiallySmall.{u + 1} Y.ProEt :=
  essentiallySmallSelf.{0} _

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients

private abbrev ordinaryTensor {A B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (f : A ⟶ B) : pbcModules Y A ⥤ pbcModules Y B :=
  SheafOfModules.ScalarReductionProof.tensorFunctor
    (K := ProEt.topology Y) (A := A) (S := B) f

private theorem ordinaryTensor_obj
    {A B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (f : A ⟶ B)
    (M : pbcModules Y A) :
    (ordinaryTensor Y f).obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} f M := by
  rfl

private def ordinaryTensorIso {A B : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (f : A ⟶ B) : pbcExtend f ≅ ordinaryTensor Y f := by
  let hc := (pbcExtensionExistence f).choose_spec.choose
  let hobj (M : pbcModules Y A) :
      (pbcExtend f).obj M = (ordinaryTensor Y f).obj M :=
    (hc M).trans (ordinaryTensor_obj Y f M).symm
  refine NatIso.ofComponents (fun M ↦ eqToIso (hobj M)) ?_
  intro M N g
  change (pbcExtend f).map g ≫ eqToHom (hobj N) =
    eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom f M g
  have hmap := (pbcExtensionExistence f).choose_spec.choose_spec.choose g
  change (pbcExtend f).map g =
    eqToHom (hc M) ≫ SheafOfModules.changeOfRingsHom f M g ≫ eqToHom (hc N).symm at hmap
  rw [hmap]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private def residueTensorIso {B k : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (q : B ⟶ k) :
    letI := SheafOfModules.monoidalCategory B
    tensorRight ((pbcRestrict q).obj
      (SheafOfModules.unit ((adicLisseForget Y).obj k))) ≅
        pbcExtend q ⋙ pbcRestrict q := by
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.monoidalCategory k
  let := SheafOfModules.symmetricCategory B
  let F := ordinaryTensor Y q
  let U := pbcRestrict q
  let K : pbcModules Y k := SheafOfModules.unit ((adicLisseForget Y).obj k)
  let e := (SheafOfModules.exists_changeOfRings_tensorCancellation q).choose
  let d : F ⋙ U ≅ tensorLeft (U.obj K) := NatIso.ofComponents
    (fun M ↦ U.mapIso (λ_ (F.obj M)).symm ≪≫ e K M) (by
      intro M N f
      change U.map (F.map f) ≫ (U.map (λ_ (F.obj N)).inv ≫ (e K N).hom) =
        (U.map (λ_ (F.obj M)).inv ≫ (e K M).hom) ≫ _
      have hunit := leftUnitor_inv_naturality (F.map f)
      have hunit' := congrArg U.map hunit
      simp only [Functor.map_comp] at hunit'
      rw [← Category.assoc, hunit']
      simp only [Category.assoc]
      congr 1
      have hn :=
        (SheafOfModules.exists_changeOfRings_tensorCancellation q).choose_spec (𝟙 K) f
      simp only [id_tensorHom] at hn
      change U.map (K ◁ F.map f) ≫ (e K N).hom =
        (e K M).hom ≫ (U.map (𝟙 K) ⊗ₘ f) at hn
      have hid : U.map (𝟙 K) = 𝟙 (U.obj K) := U.map_id K
      rw [hid, id_tensorHom] at hn
      exact hn)
  exact (BraidedCategory.tensorLeftIsoTensorRight (U.obj K)).symm ≪≫ d.symm ≪≫
    Functor.isoWhiskerRight (ordinaryTensorIso Y q).symm U

private def scalarSquareIso
    {A B C D : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    pbcExtend a ⋙ pbcExtend b ≅ pbcExtend c ⋙ pbcExtend d := by
  let e : pbcRestrict b ⋙ pbcRestrict a ≅ pbcRestrict d ⋙ pbcRestrict c :=
    pbcRestrictComp a b (c ≫ d) h ≪≫
      (pbcRestrictComp c d (c ≫ d) rfl).symm
  exact ((pbcScalarAdjunction a).comp (pbcScalarAdjunction b)).leftAdjointUniq
    (((pbcScalarAdjunction c).comp (pbcScalarAdjunction d)).ofNatIsoRight e.symm)

end TensorComparison

/-- A uniformizer layer computes scalar extension of the source residue complex,
with the target finite-quotient action restricted along reduction to its residue field.
This is a comparison in the derived category, with no constructibility or boundedness
hypothesis and no choice of a local model.

Source: parent residue-layer argument, the identification of successive powers and
balanced tensor associativity; Stacks Tag 03EK; Mathlib
Ideal.quotEquivPowQuotPowSucc.
(blueprint: lem-sf-integral-scalar-residue-layer-tensor-comparison).

Proof: write O for the target valuation ring, pi for its uniformizer and N=n+1.
Multiplication by pi^j identifies O/(pi) with (pi^j)/(pi^(j+1)) for j<N:
it is surjective by divisibility by pi^j; if pi^j*a lies in (pi^(j+1)),
cancel the nonzero pi^j in the domain O to conclude a lies in (pi).
Since (pi^N) is contained in (pi^(j+1)), quotienting first by (pi^N)
gives the same layer. Lift this linear isomorphism through ULift. Its action
by B=O/(pi^N) is the residue action via q:B->O/(pi).
The source integer inclusion carries its maximal ideal into (pi), so its action
on this layer factors through the source residue field; the induced homomorphism
is integralScalarQuotientMap at level zero. Its compatibility with the completed
projection follows from the quotient-map transition equations and the limit
projection equations. Write lambda for the layer isomorphism and f for the source
residue map. The balanced map sends (b tensor p) tensor v to
(q(b)*lambda(v)) tensor (1 tensor p). Its inverse sends
c tensor (a tensor p) to (1 tensor p) tensor lambda^(-1)(c*f(a)). These identify
the layer tensor with restriction of target residue extension of source reduction.
The formulas respect the source balancing relations, the B-action, and restrictions;
therefore they descend through sheafification. They are inverse on tensor generators,
and naturality in p makes them commute with every differential. The ordinary source
reduction functor has exactly these tensor objects and maps by its defining witness.
Localizing the resulting complex isomorphism gives the displayed derived isomorphism.
For j=0 this is the usual residue quotient; for n=0 it is the regular residue layer.
The construction is valid for zero complexes and for the empty scheme. -/
theorem integralScalarResidueLayerTensorComparison
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (j : Fin (n + 1)) :
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    let F : Fin (n + 1 + 1) → Submodule B B := fun a ↦
      (Ideal.span ({ULift.up ((Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l L (n + 1)))
          (Padic.coefficientExtensionUniformizer l L))} : Set B)) ^ (a : ℕ)
    let q : Padic.coefficientExtensionRing l L (n + 1) →+*
        Padic.coefficientExtensionRing l L 1 :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))
    let R := pbcRestrict ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} q)))
    let T := pbcExtend (integralScalarQuotientSheafMap l E L ι Y 0)
    letI := scalarReductionExtensionAdditive l E Y 0
    let C := ((scalarReductionExtension l E Y 0).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (DerivedCategory.Q.obj
      (filteredCoefficientTensorComplex Y B
        (completedIntegralCommRingSheafUnrestricted l E Y) (integralScalarRho l E L ι Y n)
        P (ModuleCat.of B ((F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype))) ≅
      DerivedCategory.Q.obj
        ((R.mapHomologicalComplex (.up ℤ)).obj
          ((T.mapHomologicalComplex (.up ℤ)).obj C))) := by
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
  let S := integralCoefficientCommRingSheaf l L Y n
  let F : Fin (n + 1 + 1) → Submodule B B := fun a ↦
    (Ideal.span ({ULift.up ((Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l L (n + 1)))
        (Padic.coefficientExtensionUniformizer l L))} : Set B)) ^ (a : ℕ)
  let V := ModuleCat.of B ((F j.castSucc) ⧸ (F j.succ).comap (F j.castSucc).subtype)
  let U := (adicLisseConstantModules Y B).obj V
  let q := integralScalarResidueProjection l L Y n
  let ρ := integralScalarRho l E L ι Y n
  let π := completedIntegralCommRingProjectionUnrestricted l E Y 0
  let f := integralScalarQuotientSheafMap l E L ι Y 0
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory S
  obtain ⟨eU⟩ := integralScalarResidueCoefficientIso (l := l) (Y := Y) (L := L) n F rfl j
  let eT : filteredCoefficientTensorFunctor Y B V ≅ pbcExtend q ⋙ pbcRestrict q :=
    SheafOfModules.siteSheafTensorRightIso S U ≪≫
      (tensoringRight (pbcModules Y S)).mapIso eU ≪≫ residueTensorIso Y q
  let := scalarReductionExtensionAdditive l E Y 0
  obtain ⟨adj, _⟩ := scalarReductionExtension_adjunction l E Y 0
  let eπ : pbcExtend π ≅ scalarReductionExtension l E Y 0 :=
    (pbcScalarAdjunction π).leftAdjointUniq adj
  let e : ordinaryTensor Y ρ ⋙ filteredCoefficientTensorFunctor Y B V ≅
      (scalarReductionExtension l E Y 0 ⋙ pbcExtend f) ⋙ pbcRestrict q :=
    Functor.isoWhiskerRight (ordinaryTensorIso Y ρ).symm
        (filteredCoefficientTensorFunctor Y B V) ≪≫
      Functor.isoWhiskerLeft (pbcExtend ρ) eT ≪≫
      (Functor.associator (pbcExtend ρ) (pbcExtend q) (pbcRestrict q)).symm ≪≫
      Functor.isoWhiskerRight
        (scalarSquareIso Y ρ q π f (integralScalarResidue_triangle l E Y L ι n).symm)
        (pbcRestrict q) ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight eπ (pbcExtend f)) (pbcRestrict q)
  let C := ((scalarReductionExtension l E Y 0).mapHomologicalComplex (.up ℤ)).obj P
  let eC : filteredCoefficientTensorComplex Y B
      (completedIntegralCommRingSheafUnrestricted l E Y) ρ P V ≅
      ((pbcRestrict q).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend f).mapHomologicalComplex (.up ℤ)).obj C) :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (P.X i)) (by
      intro i j hij
      exact (e.hom.naturality (P.d i j)).symm)
  exact ⟨DerivedCategory.Q.mapIso eC⟩

end WeilConjectures
