/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Supporting.QuotientSystemMixedCoherenceData
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Sequence.SequenceScalarGeneratorInterchange
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # A component of strict quotient-system coherence

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

-- A finite pasting calculation, independent of the module-sheaf constructions.
private theorem scalarTower_pasting
    {𝒞 : Type*} [Category* 𝒞]
    {A B C D E F G H I J K L M N O P Q R : 𝒞}
    {u : A ⟶ B} {v : B ⟶ C} {w : C ⟶ D} {z : D ⟶ E} {t : E ⟶ F}
    {d : C ⟶ G} {e : G ⟶ H} {g : H ⟶ I} {m : I ⟶ F}
    {c : B ⟶ J} {v' : J ⟶ G} {a : J ⟶ K} {b : K ⟶ L} {n : L ⟶ I}
    {s : A ⟶ M} {j : M ⟶ N} {i : N ⟶ K} {j₂ : N ⟶ O} {o : O ⟶ L}
    {h : A ⟶ P} {k : P ⟶ D} {k₁ : P ⟶ Q} {k₂ : Q ⟶ R} {k₃ : R ⟶ F}
    {α : M ⟶ Q} {δ : O ⟶ R}
    (hD : w ≫ z ≫ t = d ≫ e ≫ g ≫ m)
    (hb : c ≫ v' = v ≫ d)
    (hB : a ≫ b ≫ n = v' ≫ e ≫ g)
    (hA : u ≫ c ≫ a = s ≫ j ≫ i)
    (he : i ≫ b = j₂ ≫ o)
    (hC : k ≫ z ≫ t = k₁ ≫ k₂ ≫ k₃)
    (hd : s ≫ α = h ≫ k₁)
    (hX : α ≫ k₂ = j ≫ j₂ ≫ δ)
    (hO : o ≫ n ≫ m = δ ≫ k₃) :
    u ≫ v ≫ w ≫ z ≫ t = h ≫ k ≫ z ≫ t := by
  calc
    _ = s ≫ j ≫ j₂ ≫ o ≫ n ≫ m := by
      rw [hD, ← reassoc_of% hb, ← reassoc_of% hB,
        reassoc_of% hA, reassoc_of% he]
    _ = h ≫ k₁ ≫ k₂ ≫ k₃ := by
      rw [hO, ← reassoc_of% hX, reassoc_of% hd]
    _ = _ := by rw [hC]

-- The comparison types require repeated independent-universe sheaf instance synthesis.
/-- Source: Stacks Project, sites-cohomology.tex, Tag 0D6D.
(blueprint: lem-trf-sequence-derived-scalar-tower).
Proof: Resolve the input whole quotient system by a flat-term K-flat complex. Each scalar
extension and geometric pullback preserves the resolving class, including nonflat coefficient
extensions. Normalize each edge by its universal cochain counit and compose along both sides.
Functoriality and associativity reduce the equation to the ordinary scalar-tower generator
calculation, which sends c tensor (b tensor x) to c*j(b) tensor x on both sides. Cancel the common
composite counit and descend along the localized resolution isomorphism. This also treats equality
among any of the coefficient fields without extra assumptions. -/
theorem sequenceDerivedScalarTower
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (j : L →ₐ[ℚ_[l]] M) {X Y : Scheme.{t}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)] (f : X ⟶ Y) :
    Functor.whiskerRight (integralComparisonSystemScalarPullback l E L ι f).hom
        (integralComparisonDerivedSequenceScalar l L M j X) ≫
      Functor.whiskerLeft (integralComparisonDerivedSequenceScalar l E L ι Y)
        (integralComparisonSystemScalarPullback l L M j f).hom ≫
      Functor.whiskerRight (integralComparisonSystemScalarComposition l E L M ι j Y).hom
        (integralComparisonDerivedSequencePullback l M f) =
    Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E f)
        (integralComparisonSystemScalarComposition l E L M ι j X).hom ≫
      (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom := by
  let p := integralComparisonSequencePullback l E f
  let q := integralComparisonSequencePullback l L f
  let r := integralComparisonSequencePullback l M f
  let aY := integralComparisonSequenceScalarModel l E L ι Y
  let aX := integralComparisonSequenceScalarModel l E L ι X
  let bY := integralComparisonSequenceScalarModel l L M j Y
  let bX := integralComparisonSequenceScalarModel l L M j X
  let cY := integralComparisonSequenceScalarModel l E M (j.comp ι) Y
  let cX := integralComparisonSequenceScalarModel l E M (j.comp ι) X
  let ka : p.mapDerivedCategory ⋙ aX.T ⟶ aY.T ⋙ q.mapDerivedCategory :=
    (integralComparisonSystemScalarPullback l E L ι f).hom
  let kb : q.mapDerivedCategory ⋙ bX.T ⟶ bY.T ⋙ r.mapDerivedCategory :=
    (integralComparisonSystemScalarPullback l L M j f).hom
  let kc : p.mapDerivedCategory ⋙ cX.T ⟶ cY.T ⋙ r.mapDerivedCategory :=
    (integralComparisonSystemScalarPullback l E M (j.comp ι) f).hom
  let dY : aY.T ⋙ bY.T ⟶ cY.T := (integralComparisonSystemScalarComposition l E L M ι j Y).hom
  let dX : aX.T ⋙ bX.T ⟶ cX.T := (integralComparisonSystemScalarComposition l E L M ι j X).hom
  let A : p ⋙ aX.E ≅ aY.E ⋙ q := integralComparisonSequenceScalarPullback l E L ι f
  let B : q ⋙ bX.E ≅ bY.E ⋙ r := integralComparisonSequenceScalarPullback l L M j f
  let C : p ⋙ cX.E ≅ cY.E ⋙ r := integralComparisonSequenceScalarPullback l E M (j.comp ι) f
  let D : aY.E ⋙ bY.E ≅ cY.E := integralComparisonSequenceScalarComposition l E L ι M j Y
  let H : aX.E ⋙ bX.E ≅ cX.E := integralComparisonSequenceScalarComposition l E L ι M j X
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, e, hP, hflat, he, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) K
  let := he
  have : IsIso (DerivedCategory.Q.map e) := inferInstance
  apply (cancel_epi
    ((p.mapDerivedCategory ⋙ aX.T ⋙ bX.T).map (DerivedCategory.Q.map e))).mp
  rw [NatTrans.naturality, NatTrans.naturality]
  congr 1
  change bX.T.map (ka.app (DerivedCategory.Q.obj P)) ≫
      kb.app (aY.T.obj (DerivedCategory.Q.obj P)) ≫
        r.mapDerivedCategory.map (dY.app (DerivedCategory.Q.obj P)) =
    dX.app (p.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      kc.app (DerivedCategory.Q.obj P)
  have hpP := sequencePullback_kflatgood l E f P hP (fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E Y) (P.X n)).symm (hflat n))
  have haP := SheafOfModules.changeOfRings_isKFlat_independentCoefficients
    (integralComparisonSequenceScalarMap l E L ι Y) P aY.E aY.obj_eq aY.map_eq hP
  have hka := (integralComparisonSystemScalarPullback_existsUnique
    l E L ι f).exists.choose_spec P hP
  have hkb := (integralComparisonSystemScalarPullback_existsUnique
    l L M j f).exists.choose_spec
      ((aY.E.mapHomologicalComplex (.up ℤ)).obj P) haP
  have hkc := (integralComparisonSystemScalarPullback_existsUnique
    l E M (j.comp ι) f).exists.choose_spec P hP
  have hdY := (integralComparisonSystemScalarComposition_existsUnique
    l E L M ι j Y).exists.choose_spec P hP
  have hdX := (integralComparisonSystemScalarComposition_existsUnique
    l E L M ι j X).exists.choose_spec
      ((p.mapHomologicalComplex (.up ℤ)).obj P) hpP
  change aX.T.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      aX.ε.app ((p.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex A (.up ℤ)).hom.app P) =
    ka.app (DerivedCategory.Q.obj P) ≫ q.mapDerivedCategory.map (aY.ε.app P) ≫
      q.mapDerivedCategoryFactors.hom.app
        ((aY.E.mapHomologicalComplex (.up ℤ)).obj P) at hka
  change bX.T.map (q.mapDerivedCategoryFactors.hom.app _) ≫
      bX.ε.app ((q.mapHomologicalComplex (.up ℤ)).obj _) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex B (.up ℤ)).hom.app _) =
    kb.app (DerivedCategory.Q.obj _) ≫ r.mapDerivedCategory.map (bY.ε.app _) ≫
      r.mapDerivedCategoryFactors.hom.app
        ((bY.E.mapHomologicalComplex (.up ℤ)).obj _) at hkb
  change cX.T.map (p.mapDerivedCategoryFactors.hom.app P) ≫
      cX.ε.app ((p.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex C (.up ℤ)).hom.app P) =
    kc.app (DerivedCategory.Q.obj P) ≫ r.mapDerivedCategory.map (cY.ε.app P) ≫
      r.mapDerivedCategoryFactors.hom.app
        ((cY.E.mapHomologicalComplex (.up ℤ)).obj P) at hkc
  change dY.app (DerivedCategory.Q.obj P) ≫ cY.ε.app P =
    bY.T.map (aY.ε.app P) ≫
      bY.ε.app ((aY.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex D (.up ℤ)).hom.app P) at hdY
  change dX.app (DerivedCategory.Q.obj _) ≫ cX.ε.app _ =
    bX.T.map (aX.ε.app _) ≫ bX.ε.app ((aX.E.mapHomologicalComplex (.up ℤ)).obj _) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex H (.up ℤ)).hom.app _) at hdX
  have := cY.computes P hP
  apply (cancel_mono (r.mapDerivedCategory.map (cY.ε.app P) ≫
    r.mapDerivedCategoryFactors.hom.app
      ((cY.E.mapHomologicalComplex (.up ℤ)).obj P))).mp
  have hdY' := congrArg (fun z ↦ r.mapDerivedCategory.map z ≫
    r.mapDerivedCategoryFactors.hom.app
      ((cY.E.mapHomologicalComplex (.up ℤ)).obj P)) hdY
  simp only [Functor.map_comp, Category.assoc] at hdY'
  have nr := r.mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex D (.up ℤ)).hom.app P)
  change r.mapDerivedCategory.map (DerivedCategory.Q.map _) ≫ _ =
    _ ≫ DerivedCategory.Q.map _ at nr
  rw [nr] at hdY'
  have nb := kb.naturality (aY.ε.app P)
  change bX.T.map (q.mapDerivedCategory.map (aY.ε.app P)) ≫
      kb.app (DerivedCategory.Q.obj _) =
    kb.app (aY.T.obj (DerivedCategory.Q.obj P)) ≫
      r.mapDerivedCategory.map (bY.T.map (aY.ε.app P)) at nb
  have nd := dX.naturality (p.mapDerivedCategoryFactors.hom.app P)
  change bX.T.map (aX.T.map (p.mapDerivedCategoryFactors.hom.app P)) ≫
      dX.app (DerivedCategory.Q.obj _) =
    dX.app (p.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      cX.T.map (p.mapDerivedCategoryFactors.hom.app P) at nd
  have ne := bX.ε.naturality
    ((NatIso.mapHomologicalComplex A (.up ℤ)).hom.app P)
  change bX.T.map (DerivedCategory.Q.map _) ≫ _ =
    _ ≫ DerivedCategory.Q.map _ at ne
  have hka' := congrArg bX.T.map hka.symm
  simp only [Functor.map_comp] at hka'
  have hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using (isUnit_of_invertible (l : X.residueField x)).ne_zero
  have hY : ∀ x : Y, IsUnit (l : Y.presheaf.stalk x) := by
    intro x
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using (isUnit_of_invertible (l : Y.residueField x)).ne_zero
  have ho :
      (bX.E.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex A (.up ℤ)).hom.app P) ≫
        (NatIso.mapHomologicalComplex B (.up ℤ)).hom.app
          ((aY.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (r.mapHomologicalComplex (.up ℤ)).map
          ((NatIso.mapHomologicalComplex D (.up ℤ)).hom.app P) =
      (NatIso.mapHomologicalComplex H (.up ℤ)).hom.app
          ((p.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (NatIso.mapHomologicalComplex C (.up ℤ)).hom.app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    change bX.E.map (A.hom.app (P.X n)) ≫
        B.hom.app (aY.E.obj (P.X n)) ≫ r.map (D.hom.app (P.X n)) =
      H.hom.app (p.obj (P.X n)) ≫ C.hom.app (P.X n)
    have hn := congr_app (sequenceScalarTower_interchange l E L ι M j f hX hY) (P.X n)
    simpa only [sequenceScalarTowerLeft, sequenceScalarTowerRight,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using hn
  have ho' := congrArg DerivedCategory.Q.map ho
  simp only [Functor.map_comp] at ho'
  simpa only [Category.assoc] using
    scalarTower_pasting hdY' nb hkb hka' ne hkc.symm nd hdX ho'

end WeilConjectures
