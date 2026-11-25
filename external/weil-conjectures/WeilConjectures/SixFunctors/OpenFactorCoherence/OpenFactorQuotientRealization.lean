/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenTensorQuotient.OpenTensorQuotientData
import all WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # Augmented quotient-tower realization of open extension -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

open IntegralOnSlice

attribute [local implicit_reducible] IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.ring IntegralOnSlice.topology
  IntegralOnSlice.restrict PurCompactSupport.completed CategoryTheory.sheafCompose
  completedIntegralCommRingSheafUnrestricted Functor.sheafPushforwardContinuous
  IntegralOnSlice.tower IntegralOnSlice.level Functor.ofOpSequence Functor.ofSequence
attribute [local irreducible] IntegralOnSlice.reductionWitness

private def scalarPower (W : Scheme.{u}) (n : ℕ) :
    𝟭 (Mod l E W none) ⟶ 𝟭 (Mod l E W none) where
  app M := uniformizerPower l E W n M
  naturality {M N} f := by
    ext V x
    exact ((f.val.app V).hom.map_smul _ x).symm

-- Compatibility with a central scalar passes from a right adjoint to its left adjoint.
private theorem left_scalar {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    (a : 𝟭 A ⟶ 𝟭 A) (b : 𝟭 B ⟶ 𝟭 B)
    (h : ∀ N, G.map (b.app N) = a.app (G.obj N)) (M : A) :
    F.map (a.app M) = b.app (F.obj M) := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, h]
  exact (adj.unit.naturality (a.app M)).symm.trans
    (by simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      (a.naturality (adj.unit.app M)).symm)

private theorem publishedDirectMap {U X : Scheme.{u}} (j : U ⟶ X) :
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (proEtaleRingDirectImageMap j ((completed l E).ring X)
        ((completed l E).ring U) ((completed l E).pull j)) =
      ordinaryCompletedRingMap l E j := by
  have he : proEtaleRingDirectImageMap j ((completed l E).ring X)
      ((completed l E).ring U) ((completed l E).pull j) = sfCompletedCoefficientMap l E j := by
    exact (proEtaleSheafAdjunction j CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E j)
  rw [he]
  apply (ordinaryCompletedRingMap_existsUnique l E j).unique
  · intro n
    exact congrArg
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
      ((sfCompletedCoefficientMap_existsUnique l E j).exists.choose_spec n)
  · exact (ordinaryCompletedRingMap_existsUnique l E j).exists.choose_spec

private theorem direct_scalar {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (M : Mod l E U none) :
    (proEtaleRingModuleDirectImage j ((completed l E).ring X)
      ((completed l E).ring U) ((completed l E).pull j)).map
        ((scalarPower l E U n).app M) =
      (scalarPower l E X n).app
        ((proEtaleRingModuleDirectImage j ((completed l E).ring X)
          ((completed l E).ring U) ((completed l E).pull j)).obj M) := by
  have h := publishedDirectMap l E j
  unfold proEtaleRingModuleDirectImage
  change (⟨Functor.whiskerRight
    (proEtaleRingDirectImageMap j ((completed l E).ring X)
      ((completed l E).ring U) ((completed l E).pull j)).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩ :
    completedIntegralCoefficientSheafUnrestricted l E X ⟶
      (ordinaryRingPush.{u, u} j).obj
        (completedIntegralCoefficientSheafUnrestricted l E U)) =
      ordinaryCompletedRingMap l E j at h
  rw [h]
  ext V x
  let y : M.val.obj ((proEtaleBaseChange j).op.obj V) := x
  change uniformizerSection l E U ((proEtaleBaseChange j).op.obj V) ^ (n + 1) • y =
    (ordinaryCompletedRingMap l E j).hom.app V
      (uniformizerSection l E X V ^ (n + 1)) • y
  rw [map_pow, completed_direct_uniformizer]

-- Keep the same extension with an explicit global-slice module type.
private abbrev extension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Mod l E U none ⥤ Mod l E X none := openExtension (completed l E) j

private theorem extension_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extension l E j).Additive :=
  proEtaleRingOpenExtension_additive _ _ _ _

attribute [local instance] extension_additive

private abbrev extensionCx {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IntegralOnSlice.Cx l E U none ⥤ IntegralOnSlice.Cx l E X none :=
  (extension l E j).mapHomologicalComplex (.up ℤ)

private theorem extension_scalar {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (M : Mod l E U none) :
    (extension l E j).map ((scalarPower l E U n).app M) =
      (scalarPower l E X n).app ((extension l E j).obj M) := by
  apply left_scalar (openAdjunction (completed l E) j)
  intro N
  exact left_scalar
    (proEtaleRingModuleAdjunction j ((completed l E).ring X)
      ((completed l E).ring U) ((completed l E).pull j))
    (scalarPower l E X n) (scalarPower l E U n) (direct_scalar l E j n) N

private theorem extension_quotient_isCokernel
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (M : Mod l E U none) :
    ∃ h : uniformizerPower l E X n ((extension l E j).obj M) ≫
        (extension l E j).map ((quotientUnit l E U n).app M) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((extension l E j).map ((quotientUnit l E U n).app M)) h)) := by
  let F := extension l E j
  obtain ⟨h, ⟨hc⟩⟩ := quotientUnit_isCokernel l E U n M
  have hscalar : F.map (uniformizerPower l E U n M) =
      uniformizerPower l E X n (F.obj M) := extension_scalar l E j n M
  have : F.Additive := proEtaleRingOpenExtension_additive _ _ _ _
  have : PreservesColimits F := (openAdjunction (completed l E) j).leftAdjoint_preservesColimits
  have h' : uniformizerPower l E X n (F.obj M) ≫
      F.map ((quotientUnit l E U n).app M) = 0 := by
    rw [← hscalar, ← F.map_comp, h, F.map_zero]
  refine ⟨h', ⟨?_⟩⟩
  have hh := CokernelCofork.mapIsColimit _ hc F
  have : Epi (F.map ((quotientUnit l E U n).app M)) := epi_of_isColimit_cofork hh
  apply CokernelCofork.IsColimit.ofπ' _ h'
  intro N g hg
  have hg' : F.map (uniformizerPower l E U n M) ≫ g = 0 := by
    rw [hscalar]
    exact hg
  exact CokernelCofork.IsColimit.desc' hh g hg'

-- The two quotients are cokernels of the same uniformizer power.
private def quotientComponent {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (M : Mod l E U none) :
    (ordinaryQuotientModule l E X n).obj ((extension l E j).obj M) ≅
      (extension l E j).obj ((ordinaryQuotientModule l E U n).obj M) :=
  ((quotientUnit_isCokernel l E X n ((extension l E j).obj M)).choose_spec
    |>.some).coconePointUniqueUpToIso
      ((extension_quotient_isCokernel l E j n M).choose_spec.some)

private theorem quotientComponent_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (M : Mod l E U none) :
    (quotientUnit l E X n).app ((extension l E j).obj M) ≫
        (quotientComponent l E j n M).hom =
      (extension l E j).map ((quotientUnit l E U n).app M) := by
  let hcX := (quotientUnit_isCokernel l E X n
    ((extension l E j).obj M)).choose_spec.some
  exact hcX.comp_coconePointUniqueUpToIso_hom
    ((extension_quotient_isCokernel l E j n M).choose_spec.some) WalkingParallelPair.one

private def quotientComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) :
    extension l E j ⋙ ordinaryQuotientModule l E X n ≅
      ordinaryQuotientModule l E U n ⋙ extension l E j :=
  NatIso.ofComponents (quotientComponent l E j n) (by
    intro M N f
    have := quotientUnit_epi l E X n ((extension l E j).obj M)
    apply (cancel_epi ((quotientUnit l E X n).app
      ((extension l E j).obj M))).mp
    change (quotientUnit l E X n).app ((extension l E j).obj M) ≫
      (ordinaryQuotientModule l E X n).map ((extension l E j).map f) ≫
        (quotientComponent l E j n N).hom =
      (quotientUnit l E X n).app ((extension l E j).obj M) ≫
        (quotientComponent l E j n M).hom ≫
          (extension l E j).map ((ordinaryQuotientModule l E U n).map f)
    rw [← Category.assoc, ← (quotientUnit l E X n).naturality,
      Category.assoc, quotientComponent_unit, ← Category.assoc, quotientComponent_unit,
      Functor.id_map, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (extension l E j).map
      ((quotientUnit l E U n).naturality f))

private theorem augmentation_f (W : Scheme.{u}) (P : IntegralOnSlice.Cx l E W none)
    (n : ℕ) (i : ℤ) :
    (((IntegralOnSlice.augmentation l E W none).app P).app (op n)).f i =
      (quotientUnit l E W n).app (P.X i) := by
  ext V x
  exact ((IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec
    P n i V x).trans (unitModule_apply l E W none n (P.X i) V x).symm

private theorem augmentation_epi (W : Scheme.{u}) (P : IntegralOnSlice.Cx l E W none) (n : ℕ) :
    Epi (((IntegralOnSlice.augmentation l E W none).app P).app (op n)) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  rw [augmentation_f]
  exact quotientUnit_epi l E W n (P.X i)

private def quotientComplexComparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    extensionCx l E j ⋙ IntegralOnSlice.level l E X none n ≅
      IntegralOnSlice.level l E U none n ⋙ extensionCx l E j := by
  have : (extension l E j).Additive :=
    proEtaleRingOpenExtension_additive _ _ _ _
  have : (ordinaryQuotientModule l E X n).Additive := inferInstance
  have : (ordinaryQuotientModule l E U n).Additive := inferInstance
  exact NatIso.mapHomologicalComplex (quotientComparison l E j n) (.up ℤ)

private theorem quotientComplexComparison_unit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (P : IntegralOnSlice.Cx l E U none) :
    ((IntegralOnSlice.augmentation l E X none).app ((extensionCx l E j).obj P)).app (op n) ≫
        (quotientComplexComparison l E j n).hom.app P =
      (extensionCx l E j).map (((IntegralOnSlice.augmentation l E U none).app P).app (op n)) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    augmentation_f]
  exact quotientComponent_unit l E j n (P.X i)

-- Naturality of the augmentation forces compatibility with every tower arrow.
private def quotientTowerComparison
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    extensionCx l E j ⋙ IntegralOnSlice.tower l E X none ≅
      IntegralOnSlice.tower l E U none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (IntegralOnSlice.Cx l E U none)
          (IntegralOnSlice.Cx l E X none)).obj (extensionCx l E j) :=
  NatIso.ofComponents (fun P ↦ NatIso.ofComponents
    (fun n ↦ (quotientComplexComparison l E j n.unop).app P) (by
      intro n m f
      have := augmentation_epi l E X ((extensionCx l E j).obj P) n.unop
      apply (cancel_epi
        (((IntegralOnSlice.augmentation l E X none).app ((extensionCx l E j).obj P)).app n)).mp
      change ((IntegralOnSlice.augmentation l E X none).app
        ((extensionCx l E j).obj P)).app n ≫
          ((IntegralOnSlice.tower l E X none).obj ((extensionCx l E j).obj P)).map f ≫
            (quotientComplexComparison l E j m.unop).hom.app P =
        ((IntegralOnSlice.augmentation l E X none).app
          ((extensionCx l E j).obj P)).app n ≫
            (quotientComplexComparison l E j n.unop).hom.app P ≫
              (extensionCx l E j).map ((IntegralOnSlice.tower l E U none).obj P |>.map f)
      rw [← Category.assoc]
      have hX := ((IntegralOnSlice.augmentation l E X none).app
        ((extensionCx l E j).obj P)).naturality f
      change 𝟙 _ ≫ _ = _ at hX
      rw [Category.id_comp] at hX
      rw [← hX, quotientComplexComparison_unit]
      rw [← Category.assoc, quotientComplexComparison_unit, ← Functor.map_comp]
      have hU := ((IntegralOnSlice.augmentation l E U none).app P).naturality f
      change 𝟙 _ ≫ _ = _ at hU
      rw [Category.id_comp] at hU
      exact congrArg (extensionCx l E j).map hU)) (by
    intro P Q f
    apply NatTrans.ext
    funext n
    exact (quotientComplexComparison l E j n.unop).hom.naturality f)

private theorem quotientTowerComparison_unique
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (v : extensionCx l E j ⋙ IntegralOnSlice.tower l E X none ⟶
      IntegralOnSlice.tower l E U none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (IntegralOnSlice.Cx l E U none)
          (IntegralOnSlice.Cx l E X none)).obj (extensionCx l E j))
    (hv : ∀ (P : IntegralOnSlice.Cx l E U none) (n : ℕ),
      ((IntegralOnSlice.augmentation l E X none).app ((extensionCx l E j).obj P)).app
          (op n) ≫ (v.app P).app (op n) =
        (extensionCx l E j).map
          (((IntegralOnSlice.augmentation l E U none).app P).app (op n))) :
    v = (quotientTowerComparison l E j).hom := by
  apply NatTrans.ext
  funext P
  apply NatTrans.ext
  funext n
  have := augmentation_epi l E X ((extensionCx l E j).obj P) n.unop
  apply (cancel_epi
    (((IntegralOnSlice.augmentation l E X none).app ((extensionCx l E j).obj P)).app n)).mp
  exact (hv P n.unop).trans (quotientComplexComparison_unit l E j n.unop P).symm

/-- The augmented extension tower, before derived localization.
Source: Stacks 0E8I, 099N, 09BP; blueprint proposition-composition-base-change-rf-shriek--1, open
factor. (blueprint: lem-sf-open-factor-quotient-realization).

Proof: identify the completed slice coefficients by the constant-section and quotient
projection equations of o. The scalar compatibility q.scalar and q.strictScalar
then transport to the published termwise extension. The global slice tower is the
unrestricted positive-exponent tower, with the same transitions, so this gives t.
At every degree its map sends the quotient tensor generator to the extended tensor
generator. The scalar units give ht. The quotient projection is surjective as a
sheaf map: locally a quotient coefficient lifts to a completed coefficient, which
can be moved across the balanced tensor. Hence precomposition with each component
of the quotient augmentation is injective on module maps. Apply this degreewise,
then natural-transformation extensionality, to obtain uniqueness of t.hom.
The comparison is constructed on entire strict complex systems; no inference
from separate derived evaluations is involved. This statement concerns only
ordinary quotient tensors and their augmentation, and asserts no commutation
with completion, geometric constructibility or tensor projection formula. -/
theorem openFactorQuotientRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : IntegralOpenReduction.Operations l E j)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
    (c : IntegralOpenReduction.Comparison l E j o SX SU st)
    (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c) :
    ∃ t : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ≅
        IntegralOnSlice.tower.{u, u} l E U none ⋙
          (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j),
      (∀ (P : Cx l E U) (n : ℕ),
        ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
            (op n) ≫ (t.hom.app P).app (op n) =
          (jCx l E j).map
            (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))) ∧
      (∀ v : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ⟶
          IntegralOnSlice.tower.{u, u} l E U none ⋙
            (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j),
        (∀ (P : Cx l E U) (n : ℕ),
          ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
              (op n) ≫ (v.app P).app (op n) =
            (jCx l E j).map
              (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))) →
        v = t.hom) := by
  -- Construct the strict comparison directly from scalar cokernels.
  have _ := q
  refine ⟨quotientTowerComparison l E j, ?_, ?_⟩
  · exact fun P n ↦ quotientComplexComparison_unit l E j n P
  · exact quotientTowerComparison_unique l E j

end WeilConjectures.OpenFactorCoherence
