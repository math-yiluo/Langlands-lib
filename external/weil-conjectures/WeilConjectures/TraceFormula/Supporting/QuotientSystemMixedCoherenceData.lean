/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.Finite.FiniteSystemPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.PathCategory.Basic
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
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement

/-! # Data for mixed geometric and scalar coherence on strict quotient systems

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D and the generator calculations
of the DAG node (blueprint: lem-trf-quotient-system-mixed-coherence).

The equations are asserted both before localization and in the unbounded derived
categories of entire quotient diagrams. Finite geometric coherence quantifies over
all binary assemblies of an arbitrary path, including the empty path. No realization,
normalization, boundedness, Tor-amplitude or flatness assumption is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u a v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  integralComparisonSequenceScalarModel

-- Select the sequence-site instances without constraining the coefficient universe.
attribute [local instance 5000] coefficientSequenceEssentiallySmall
attribute [local instance 6000] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.moduleAbelian SemilinearSections.hasDerived
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  finiteSystemSequenceSmall finiteSystemSiteSmall
attribute [local irreducible] HasDerivedCategory.standard

private theorem sequenceDerived_ext
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) {D : Type a} [Category.{v} D]
    {F G : coefficientSequenceDerived l E X ⥤ D} (α β : F ⟶ G)
    (h : ∀ P : CochainComplex (coefficientSequenceModules l E X) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P →
      α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P)) : α = β := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro K
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E X) K
  let := hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  apply (cancel_epi (F.map (DerivedCategory.Q.map f))).mp
  rw [α.naturality, β.naturality, h P hP]

section ScalarComparisons

variable (l : ℕ) [Fact l.Prime]
  (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)

/-- The scalar associator is uniquely determined by its ordinary tensor formula and
universal cochain counits. Source: Stacks 06YY, 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence).
Proof: resolve an input by one flat-term K-flat complex on the sequence site.
Ordinary extension preserves these complexes, including under successive coefficient
maps. The three universal counits are therefore invertible. Conjugate the localization
of the ordinary associator, c tensor (b tensor x) to c*j(b) tensor x, by these counits.
Naturality and the universal derived property descend this map to the localization;
the inverse ordinary associator gives its inverse. Cancellation of the resolution
isomorphisms proves uniqueness. The calculation uses neither flatness of the ring maps
nor a bound on the input complex. -/
theorem integralComparisonSystemScalarComposition_existsUnique (X : Scheme.{t}) :
    ∃! a : integralComparisonDerivedSequenceScalar l E L ι X ⋙
        integralComparisonDerivedSequenceScalar l L M j X ≅
      integralComparisonDerivedSequenceScalar l E M (j.comp ι) X,
      ∀ (P : CochainComplex (coefficientSequenceModules l E X) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X) P →
        a.hom.app (DerivedCategory.Q.obj P) ≫
            (integralComparisonSequenceScalarModel l E M (j.comp ι) X).ε.app P =
          (integralComparisonDerivedSequenceScalar l L M j X).map
              ((integralComparisonSequenceScalarModel l E L ι X).ε.app P) ≫
            (integralComparisonSequenceScalarModel l L M j X).ε.app
              (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
                (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (integralComparisonSequenceScalarComposition l E L ι M j X)
                  (.up ℤ)).hom.app P) := by
  let A := coefficientSequenceModules l E X
  let ma := integralComparisonSequenceScalarModel l E L ι X
  let mb := integralComparisonSequenceScalarModel l L M j X
  let mc := integralComparisonSequenceScalarModel l E M (j.comp ι) X
  let e := integralComparisonSequenceScalarComposition l E L ι M j X
  let δ : DerivedCategory.Q ⋙ (ma.T ⋙ mb.T) ⟶
      mc.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := Functor.whiskerRight ma.ε mb.T ≫
    Functor.whiskerLeft (ma.E.mapHomologicalComplex (.up ℤ)) mb.ε ≫
    Functor.whiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)).hom DerivedCategory.Q
  let := mc.universal
  let c := mc.T.leftDerivedLift mc.ε (HomologicalComplex.quasiIso A (.up ℤ))
    (ma.T ⋙ mb.T) δ
  have hc (P : CochainComplex A ℤ) :
      c.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P =
        mb.T.map (ma.ε.app P) ≫ mb.ε.app
          ((ma.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) :=
    mc.T.leftDerived_fac_app mc.ε (HomologicalComplex.quasiIso A (.up ℤ)) _ δ P
  have hciso (P : CochainComplex A ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P)
      (hflat : ∀ n : ℤ, exactFunctor _ _
        (@MonoidalCategory.tensorRight _ _
          (SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E X)) (P.X n))) :
      IsIso (c.app (DerivedCategory.Q.obj P)) := by
    have hPa := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (integralComparisonSequenceScalarMap l E L ι X) P ma.E ma.obj_eq ma.map_eq hP hflat).1
    have := ma.computes P hP
    have := mb.computes _ hPa
    have := mc.computes P hP
    have : IsIso (c.app (DerivedCategory.Q.obj P) ≫ mc.ε.app P) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (mc.ε.app P)
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    let P := DerivedCategory.Q.objPreimage K
    rw [NatTrans.isIso_app_iff_of_iso c (DerivedCategory.Q.objObjPreimageIso K).symm]
    obtain ⟨R, f, hR, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E X) P
    let := hf
    have : IsIso (DerivedCategory.Q.map f) := inferInstance
    have := hciso R hR hflat
    have h := c.naturality (DerivedCategory.Q.map f)
    have : IsIso (((ma.T ⋙ mb.T).map (DerivedCategory.Q.map f)) ≫
        c.app (DerivedCategory.Q.obj P)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((ma.T ⋙ mb.T).map (DerivedCategory.Q.map f)) _
  refine ⟨asIso c, fun P _ ↦ hc P, ?_⟩
  intro b hb
  apply Iso.ext
  apply sequenceDerived_ext l E X b.hom c
  intro P hP
  have := mc.computes P hP
  apply (cancel_mono (mc.ε.app P)).mp
  exact (hb P hP).trans (hc P).symm

/-- The canonical derived associator, with multiplication normalization before localization.
Source: Stacks 06YY, 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralComparisonSystemScalarComposition (X : Scheme.{t}) :
    integralComparisonDerivedSequenceScalar l E L ι X ⋙
      integralComparisonDerivedSequenceScalar l L M j X ≅
        integralComparisonDerivedSequenceScalar l E M (j.comp ι) X :=
  (integralComparisonSystemScalarComposition_existsUnique l E L M ι j X).exists.choose

/-- The derived scalar unit is the localization of multiplication, with its canonical
cochain counit. Source: Stacks 06YY
(blueprint: lem-trf-quotient-system-mixed-coherence).
Proof: on a K-flat representative localize the ordinary multiplication unitor and
precede it by the universal derived counit. This is invertible there. K-flat resolutions
and naturality extend it to every derived object; cancellation of each resolution
isomorphism gives uniqueness. The inverse inserts the scalar one. -/
theorem integralComparisonSystemScalarUnit_existsUnique (X : Scheme.{t}) :
    ∃! a : integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _,
      ∀ (P : CochainComplex (coefficientSequenceModules l E X) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E X) P →
        a.hom.app (DerivedCategory.Q.obj P) =
          (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).ε.app P ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                (integralComparisonSequenceScalarUnit l E X) (.up ℤ)).hom.app P) := by
  let A := coefficientSequenceModules l E X
  let m := integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X
  let e := integralComparisonSequenceScalarUnit l E X
  let d : m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q :=
    Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q
  let β : DerivedCategory.Q ⋙ 𝟭 (coefficientSequenceDerived l E X) ⟶
      m.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := d.inv
  let := m.universal
  let : (𝟭 (coefficientSequenceDerived l E X)).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso A (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (asIso β)
  let c := Functor.leftDerivedNatIso m.T (𝟭 _) m.ε β
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _)
  have hc (P : CochainComplex A ℤ) :
      c.hom.app (DerivedCategory.Q.obj P) = m.ε.app P ≫ d.hom.app P := by
    have h := Functor.leftDerivedNatTrans_app m.T (𝟭 _) m.ε β
      (HomologicalComplex.quasiIso A (.up ℤ)) (𝟙 _) P
    change c.hom.app (DerivedCategory.Q.obj P) ≫ d.inv.app P = m.ε.app P ≫ 𝟙 _ at h
    simpa using congrArg (fun f ↦ f ≫ d.hom.app P) h
  refine ⟨c, fun P _ ↦ hc P, ?_⟩
  intro b hb
  apply Iso.ext
  exact sequenceDerived_ext l E X b.hom c.hom (fun P hP ↦ (hb P hP).trans (hc P).symm)

/-- The derived scalar multiplication unitor on the whole quotient diagram.
Source: Stacks 06YY (blueprint: lem-trf-quotient-system-mixed-coherence). -/
def integralComparisonSystemScalarUnit (X : Scheme.{t}) :
    integralComparisonDerivedSequenceScalar l E E (AlgHom.id ℚ_[l] E) X ≅
      𝟭 (coefficientSequenceDerived l E X) :=
  (integralComparisonSystemScalarUnit_existsUnique l E X).exists.choose

end ScalarComparisons

attribute [local irreducible] integralComparisonSystemScalarComposition
  integralComparisonSystemScalarUnit

/-- Every scheme occurring in the finite string has ell invertible.
Source: the standing scheme hypothesis of the node
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
def IntegralQuotientPathInvertible (l : ℕ) {X : Scheme.{t}} :
    ∀ {Y : Scheme.{t}}, Quiver.Path X Y → Prop
  | _, .nil => ∀ x : X, Nonempty (Invertible (l : X.residueField x))
  | Y, .cons p _ => IntegralQuotientPathInvertible l p ∧
      ∀ y : Y, Nonempty (Invertible (l : Y.residueField y))

/-- Binary parenthesizations of a fixed finite string, with empty pieces permitted.
Source: the finite-string assertion of the node, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
inductive IntegralQuotientBracketing :
    {X Y : Scheme.{t}} → Quiver.Path X Y → Type (t + 1)
  | nil (X : Scheme.{t}) : IntegralQuotientBracketing (Quiver.Path.nil : Quiver.Path X X)
  | single {X Y : Scheme.{t}} (f : X ⟶ Y) : IntegralQuotientBracketing f.toPath
  | comp {X Y Z : Scheme.{t}} {p : Quiver.Path X Y} {q : Quiver.Path Y Z}
      (a : IntegralQuotientBracketing p) (b : IntegralQuotientBracketing q) :
      IntegralQuotientBracketing (p.comp q)

/-- Interpret the parenthesized string by iterated pullback, retaining its entire diagram.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
@[reducible]
def integralQuotientBracketFunctor
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p) :
    D Y ⥤ D X :=
  match b with
  | .nil _ => 𝟭 _
  | .single f => U f
  | .comp a b =>
      integralQuotientBracketFunctor D U b ⋙ integralQuotientBracketFunctor D U a
termination_by structural b

/-- The comparison associated to a parenthesization, recursively using only the given
canonical compositor and inverse-image unitor. Equal composites use equality transport.
Source: finite-string clause, Stacks 0D6D
(blueprint: lem-trf-quotient-system-mixed-coherence). -/
@[reducible]
def integralQuotientBracketComparison
    (D : Scheme.{t} → Type a) [∀ X : Scheme.{t}, Category.{v} (D X)]
    (U : ∀ {X Y : Scheme.{t}}, (X ⟶ Y) → (D Y ⥤ D X))
    (c : ∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z), U (f ≫ g) ≅ U g ⋙ U f)
    (e : ∀ X : Scheme.{t}, U (𝟙 X) ≅ 𝟭 (D X))
    {X Y : Scheme.{t}} {p : Quiver.Path X Y} (b : IntegralQuotientBracketing p) :
    U (CategoryTheory.composePath p) ≅ integralQuotientBracketFunctor D U b :=
  match b with
  | .nil X => e X
  | .single f =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_toPath f))
  | .comp (p := p) (q := q) a b =>
      eqToIso (congrArg (fun g ↦ U g) (CategoryTheory.composePath_comp p q)) ≪≫
        c (CategoryTheory.composePath p) (CategoryTheory.composePath q) ≪≫
        Functor.isoWhiskerLeft (U (CategoryTheory.composePath q))
          (integralQuotientBracketComparison D U c e a) ≪≫
        Functor.isoWhiskerRight (integralQuotientBracketComparison D U c e b)
          (integralQuotientBracketFunctor D U a)
termination_by structural b

attribute [local irreducible] integralComparisonSequenceComposition integralComparisonSequenceUnit
  integralComparisonSequenceScalarPullback integralComparisonSequenceScalarComposition
  integralComparisonSequenceScalarUnit integralComparisonSystemComposition
  integralComparisonSystemUnit integralComparisonSystemScalarPullback

end WeilConjectures
