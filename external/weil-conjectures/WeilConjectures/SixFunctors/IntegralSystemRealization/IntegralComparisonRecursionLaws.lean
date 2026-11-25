/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus

/-! # Natural comparison recursion for integral realization
Source: blueprint fix-prop-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem counitIso (W : Scheme.{u}) (M : System l E W)
    (hM : Good l E W M) : IsIso ((calculus l E W).adjunction.counit.app M) :=
  ((purNormalizedReconstructionOfScheme l E W (calculus l E W)).1 M hM.1).2

private theorem inputUnitIso (W : Scheme.{u}) (K : Integral l E W)
    (hK : sfIntegralConstructible l E W K) :
    IsIso ((calculus l E W).adjunction.unit.app K) := by
  apply (purNormalizedReconstructionOfScheme l E W (calculus l E W)).2 K
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ D.p := by change l ≠ p; omega
  exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E W D hl K).mp hK.1⟩

private def counitComparison {C : Type v} [Category.{w} C]
    (W : Scheme.{u}) (F : C ⥤ System l E W)
    (hF : ∀ K, Good l E W (F.obj K)) :
    F ⋙ coefficientSequenceLimit l E W ⋙ (calculus l E W).reduction ≅ F := by
  let ε := Functor.whiskerLeft F (calculus l E W).adjunction.counit
  have : ∀ K, IsIso (ε.app K) := fun K ↦ counitIso l E W _ (hF K)
  exact NatIso.ofComponents (fun K ↦ asIso (ε.app K)) (fun f ↦ ε.naturality f)

private def pullStep {C : Type v} [Category.{w} C]
    {U V : Scheme.{u}} (f : U ⟶ V) (F : C ⥤ System l E V)
    (hF : ∀ K, Good l E V (F.obj K)) :
    F ⋙ pull l E f ⋙ coefficientSequenceLimit l E U ≅
      F ⋙ coefficientSequenceLimit l E V ⋙ integralDerivedPullback l E f :=
  (Functor.isoWhiskerRight (counitComparison l E V F hF)
    (pull l E f ⋙ coefficientSequenceLimit l E U)).symm ≪≫
  Functor.isoWhiskerLeft (F ⋙ coefficientSequenceLimit l E V)
    (pullbackTensorIntegralPullbackModel l E f).symm

private def tensorStep {C : Type v} [Category.{w} C]
    (W : Scheme.{u}) (F G : C ⥤ System l E W)
    (hF : ∀ K, Good l E W (F.obj K)) (hG : ∀ K, Good l E W (G.obj K)) :
    F.prod' G ⋙ (calculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W ≅
      (F ⋙ coefficientSequenceLimit l E W).prod'
        (G ⋙ coefficientSequenceLimit l E W) ⋙ integralCompletedTensor l E W := by
  let ε : (F ⋙ coefficientSequenceLimit l E W ⋙ (calculus l E W).reduction).prod'
      (G ⋙ coefficientSequenceLimit l E W ⋙ (calculus l E W).reduction) ≅ F.prod' G :=
    NatIso.ofComponents (fun K ↦ Iso.prod
      ((counitComparison l E W F hF).app K) ((counitComparison l E W G hG).app K))
      (fun f ↦ by ext <;> exact (calculus l E W).adjunction.counit.naturality _)
  exact (Functor.isoWhiskerRight ε
    ((calculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W)).symm ≪≫
    Functor.isoWhiskerLeft ((F ⋙ coefficientSequenceLimit l E W).prod'
      (G ⋙ coefficientSequenceLimit l E W)) (pullbackTensorIntegralTensorModel l E W).symm

private theorem normalizedNaturality
    {C A : Type*} [Category C] [Category A]
    {F F' G G' : C ⥤ A} (q : F' ⟶ F) (η : G ⟶ G') (r : F' ⟶ G')
    (d : ∀ K, F.obj K ≅ G.obj K)
    (h : ∀ K, q.app K ≫ (d K).hom ≫ η.app K = r.app K)
    [∀ K, IsIso (q.app K)] [∀ K, IsIso (η.app K)]
    {K N : C} (f : K ⟶ N) : F.map f ≫ (d N).hom = (d K).hom ≫ G.map f := by
  apply (cancel_epi (q.app K)).1
  apply (cancel_mono (η.app N)).1
  calc
    (q.app K ≫ (F.map f ≫ (d N).hom)) ≫ η.app N =
        F'.map f ≫ (q.app N ≫ (d N).hom ≫ η.app N) := by
      rw [← Category.assoc, ← q.naturality f]
      simp only [Category.assoc]
    _ = F'.map f ≫ r.app N := by rw [h N]
    _ = r.app K ≫ G'.map f := r.naturality f
    _ = (q.app K ≫ ((d K).hom ≫ G.map f)) ≫ η.app N := by
      rw [← h K]
      simp only [Category.assoc, η.naturality f]

private def openStep {C : Type v} [Category.{w} C]
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (F : C ⥤ System l E U) (hF : ∀ K, Good l E U (F.obj K))
    (hJ : ∀ K, Good l E V ((Operations.shriek l E o j).obj (F.obj K))) :
    F ⋙ Operations.shriek l E o j ⋙ coefficientSequenceLimit l E V ≅
      F ⋙ coefficientSequenceLimit l E U ⋙ ringedOpen l E j := by
  let d := fun K ↦ a.openRealization j inferInstance (F.obj K) (hF K) (hJ K)
  let q := Functor.whiskerRight
    (Functor.whiskerLeft F (calculus l E U).adjunction.counit)
    (Operations.shriek l E o j ⋙ coefficientSequenceLimit l E V)
  let η := Functor.whiskerLeft
    (F ⋙ coefficientSequenceLimit l E U ⋙ ringedOpen l E j)
    (calculus l E V).adjunction.unit
  let r := Functor.whiskerLeft (F ⋙ coefficientSequenceLimit l E U)
    (Functor.whiskerRight (a.realizationModel.openReduction l E j)
      (coefficientSequenceLimit l E V))
  have hq : ∀ K, IsIso (q.app K) := by
    intro K
    have := counitIso l E U (F.obj K) (hF K)
    exact inferInstanceAs (IsIso ((coefficientSequenceLimit l E V).map
      ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app (F.obj K)))))
  have hη : ∀ K, IsIso (η.app K) := by
    intro K
    have := counitIso l E V _ (hJ K)
    have ht : IsIso ((calculus l E V).adjunction.unit.app
        ((coefficientSequenceLimit l E V).obj
          ((Operations.shriek l E o j).obj (F.obj K)))) := by
      have htri := (calculus l E V).adjunction.right_triangle_components
        ((Operations.shriek l E o j).obj (F.obj K))
      have hi : IsIso ((calculus l E V).adjunction.unit.app
          ((coefficientSequenceLimit l E V).obj
            ((Operations.shriek l E o j).obj (F.obj K))) ≫
          (coefficientSequenceLimit l E V).map
            ((calculus l E V).adjunction.counit.app _)) := by
        rw [htri]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _
        ((coefficientSequenceLimit l E V).map
          ((calculus l E V).adjunction.counit.app _))
    have hn := (calculus l E V).adjunction.unit.naturality (d K).hom
    have hi : IsIso ((d K).hom ≫ η.app K) := by
      change IsIso ((d K).hom ≫ (calculus l E V).adjunction.unit.app _)
      rw [show (d K).hom ≫ (calculus l E V).adjunction.unit.app _ = _ from hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (d K).hom _
  exact NatIso.ofComponents d (normalizedNaturality q η r d
    (fun K ↦ a.openNormalization j (F.obj K) (hF K) (hJ K)))

private def comparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o)
    {I : Type u} [Finite I] {X : I → Over (Spec (.of D.k))} :
    {W : Over (Spec (.of D.k))} → (e : Expression _ I X W) → e.geometric →
      (e.realizationSource l E o ≅ e.realizationTarget l E o)
  | _, .var i, _ => by
    let F := ((Expression.var (X := X) i).domain l E o).ι ⋙ Pi.eval _ i
    let η := Functor.whiskerLeft F (calculus l E (X i).left).adjunction.unit
    have : ∀ K, IsIso (η.app K) := fun K ↦
      inputUnitIso l E (X i).left (K.obj i) (K.property.1 i).1
    exact (NatIso.ofComponents (fun K ↦ asIso (η.app K))
      (fun f ↦ η.naturality f)).symm
  | _, .pull f e, g => by
    let child : ((Expression.pull f e).domain l E o).FullSubcategory ⥤
        (e.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2⟩)
    let F := ((Expression.pull f e).domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    exact pullStep l E f.left F
      (fun K ↦ e.admissibleGood l E o _ K.property.2.2) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft child (comparison D hl o a e g.2.2.2.2.2))
        (integralDerivedPullback l E f.left)
  | _, .push f hp e, g => by
    let child : ((Expression.push f hp e).domain l E o).FullSubcategory ⥤
        (e.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2⟩)
    let F := ((Expression.push f hp e).domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    exact Functor.isoWhiskerLeft F (a.realizationModel.push l E f.left) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft child (comparison D hl o a e g.2.2))
        (ringedPush l E f.left)
  | _, .shriek j hj hq e, g => by
    letI := hj
    letI := hq
    let child : ((Expression.shriek j hj hq e).domain l E o).FullSubcategory ⥤
        (e.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2⟩)
    let F := ((Expression.shriek j hj hq e).domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    exact openStep l E o a j.left F
      (fun K ↦ e.admissibleGood l E o _ K.property.2.2)
      (fun K ↦ K.property.2.1) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft child (comparison D hl o a e g.2.2))
        (ringedOpen l E j.left)
  | W, .tensor e t, g => by
    let child₁ : ((Expression.tensor e t).domain l E o).FullSubcategory ⥤
        (e.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2.1⟩)
    let child₂ : ((Expression.tensor e t).domain l E o).FullSubcategory ⥤
        (t.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2.2⟩)
    let F := ((Expression.tensor e t).domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    let G := ((Expression.tensor e t).domain l E o).ι ⋙ inputReduction l E X ⋙
      t.evaluate (systemInterpretation l E o)
    let ce := Functor.isoWhiskerLeft child₁ (comparison D hl o a e g.2.2.1)
    let ct := Functor.isoWhiskerLeft child₂ (comparison D hl o a t g.2.2.2)
    let pair := (prodFunctorToFunctorProd _ _ _).mapIso (Iso.prod ce ct)
    exact tensorStep l E W.left F G
      (fun K ↦ e.admissibleGood l E o _ K.property.2.2.1)
      (fun K ↦ t.admissibleGood l E o _ K.property.2.2.2) ≪≫
      Functor.isoWhiskerRight pair (integralCompletedTensor l E W.left)
  | _, .compactSupport f c e, g => by
    letI : QuasiCompact c.i := compactOpenQuasiCompact c g.2.2.2.2.1
    let child : ((Expression.compactSupport f c e).domain l E o).FullSubcategory ⥤
        (e.domain l E o).FullSubcategory :=
      ObjectProperty.ιOfLE (fun K h ↦ ⟨h.1, h.2.2.1⟩)
    let F := ((Expression.compactSupport f c e).domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o)
    exact Functor.isoWhiskerLeft (F ⋙ Operations.shriek l E o c.i)
        (a.realizationModel.push l E c.g) ≪≫
      Functor.isoWhiskerRight
        (openStep l E o a c.i F
          (fun K ↦ e.admissibleGood l E o _ K.property.2.2.1)
          (fun K ↦ K.property.2.2.2)) (ringedPush l E c.g) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft child (comparison D hl o a e g.2.2.2.2.2))
        (ringedOpen l E c.i ⋙ ringedPush l E c.g)

/-- Natural comparison recursion for the specified canonical ambient models.
Only the variable, unary, tensor and chosen compactification formulas are asserted;
there is no statement about structural-generator maps or finite projections.
Source: blueprint fix-prop-coherence, expression-tree construction, and
lem-sf-integral-basic-realization / lem-sf-integral-expression-recursion
(blueprint: lem-sf-integral-comparison-recursion-laws).

Proof: reconstruct the actual unit on complete inputs and the actual counit on
normalized systems. At a leaf invert that unit. For pullback insert the inverse
of L P applied to the counit and then the published K-flat comparison; for tensor
use the pair of counits and the published tensor comparison. Their displayed
laws follow by inverse cancellation. Proper image uses the given ambient
right-adjoint conjugate directly. The given open realization is natural: its
normalization equation is q d u = L r, where q is L J of the counit. The maps q,
u and L r are natural. Both q and u are invertible: q by normalization of the
input, and u by the triangle identity on L J M and transport along d. Cancel
these in the naturality equation to obtain naturality of d.

Recurse on the finite expression tree, restricting each child comparison along
the full-domain inclusion. Whiskering and composition preserve naturality and
invertibility, including at repeated variables. Compact support uses the given
open comparison followed by the given proper comparison, retaining the hidden
open intermediate and its Good witness. All six laws follow from these exact
formulas. No constructibility-to-Tor implication, generator square, or finite
projection assertion is used. -/
theorem integralComparisonRecursionLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o) :
    ∃ c : ExpressionRecursion.Comparisons l E D o, Nonempty (RecursionLaws l E D o a c) := by
  refine ⟨fun e g ↦ comparison l E D hl o a e g, ⟨?_⟩⟩
  constructor
  · intro I _ X i g K
    have := inputUnitIso l E (X i).left (K.obj i) (K.property.1 i).1
    simp only [comparison, Iso.symm_hom, NatIso.ofComponents_inv_app, asIso_inv]
    exact IsIso.hom_inv_id _
  · intro I _ X U V f hp e ge g K
    rfl
  · intro I _ X U V f e ge g K
    have := counitIso l E V.left _
      (e.admissibleGood l E o _ K.property.2.2)
    let ε := (calculus l E V.left).adjunction.counit.app
      ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
    let q := (coefficientSequenceLimit l E U.left).map ((pull l E f.left).map ε)
    simp only [comparison, pullStep, counitComparison, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatIso.ofComponents_inv_app, asIso_inv,
      Functor.comp_map, Functor.map_inv, Category.assoc]
    change q ≫ (inv q ≫ _ ≫ _) = _
    rw [IsIso.hom_inv_id_assoc]
    rfl
  · intro I _ X U V j hj hq e ge g K
    rfl
  · intro I _ X W e t ge gt g K
    have := counitIso l E W.left _
      (e.admissibleGood l E o _ K.property.2.2.1)
    have := counitIso l E W.left _
      (t.admissibleGood l E o _ K.property.2.2.2)
    let ε := Iso.prod
      (asIso ((calculus l E W.left).adjunction.counit.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))))
      (asIso ((calculus l E W.left).adjunction.counit.app
        ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))))
    let T := (calculus l E W.left).systemClosed.tensor
    let L := coefficientSequenceLimit l E W.left
    simp only [comparison, tensorStep, counitComparison, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatIso.ofComponents_inv_app, Functor.comp_map,
      Category.assoc]
    change L.map (T.map ε.hom) ≫ (L.map (T.map ε.inv) ≫ _ ≫ _) = _
    rw [← L.map_comp_assoc, ← T.map_comp, ε.hom_inv_id, T.map_id, L.map_id,
      Category.id_comp]
    rfl
  · intro I _ X U V f c e ge g K
    simp only [comparison, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.map_comp]
    rfl

end WeilConjectures.IntegralSystemRealization
