/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexCoefficientTransition
public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexSubstitution
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisons
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCompletionNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingSignedRoosShift
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorConstruction
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorFamilyCoherence
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSignedShifts
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransition
import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorSubstitution

/-! # Projection-normalized reindexing of completion and completed tensor

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-completion-unit-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private theorem podOrdinaryToCompleted_isIso
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.CompleteUnit l E g D)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (hK : IntegralOnSlice.IsComplete l E Y none K) :
    IsIso ((podOrdinaryToCompleted l E g D).app K) := by
  have : IsIso ((podReindexCalculus l E Y).adjunction.unit.app K) := hD K hK
  dsimp only [podOrdinaryToCompleted, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app]
  infer_instance

private theorem podCompleteUnit
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) : PodCompletionReindex.CompleteUnit l E g D := by
  have hl : IsUnit (l : Γ(Y, ⊤)) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ (l : Γ(Y, ⊤)) (fun y _ ↦ by
      apply isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y))
      simpa only [map_natCast] using isUnit_of_invertible (l : Y.residueField y))
  exact (purNormalizedReconstruction l E Y hl (podReindexCalculus l E Y)).2

private theorem podCounit_of_unit (D : PodCompletionReindex l E g)
    (hunit : PodCompletionReindex.Unit l E g D) :
    PodCompletionReindex.Counit l E g D := by
  intro N
  let SY := podReindexCalculus l E Y
  let SX := podReindexCalculus l E X
  let F := podOrdinaryReindex l E g
  let G := integralComparisonDerivedSequencePullback l E g
  let LY := coefficientSequenceLimit l E Y
  let LX := coefficientSequenceLimit l E X
  apply (SX.adjunction.homEquiv _ _).injective
  change SX.adjunction.unit.app (F.obj (LY.obj N)) ≫
      LX.map (D.reduction.inv.app (LY.obj N) ≫ G.map (SY.adjunction.counit.app N)) =
    SX.adjunction.unit.app (F.obj (LY.obj N)) ≫
      LX.map (SX.reduction.map (D.limit.hom.app N) ≫ SX.adjunction.counit.app (G.obj N))
  have hleft : SX.adjunction.unit.app (F.obj (LY.obj N)) ≫
      LX.map (D.reduction.inv.app (LY.obj N) ≫ G.map (SY.adjunction.counit.app N)) =
      D.limit.hom.app N := by
    rw [← hunit (LY.obj N)]
    simp only [Category.assoc]
    change F.map (SY.adjunction.unit.app (LY.obj N)) ≫
      D.limit.hom.app (SY.reduction.obj (LY.obj N)) ≫
        LX.map (D.reduction.hom.app (LY.obj N)) ≫
          LX.map (D.reduction.inv.app (LY.obj N) ≫ G.map (SY.adjunction.counit.app N)) = _
    rw [← LX.map_comp, Iso.hom_inv_id_app_assoc]
    have hn := D.limit.hom.naturality (SY.adjunction.counit.app N)
    change F.map (LY.map (SY.adjunction.counit.app N)) ≫ D.limit.hom.app N =
      D.limit.hom.app (SY.reduction.obj (LY.obj N)) ≫
        LX.map (G.map (SY.adjunction.counit.app N)) at hn
    rw [← hn, ← Category.assoc, ← F.map_comp, SY.adjunction.right_triangle_components]
    exact (congrArg (· ≫ D.limit.hom.app N) (F.map_id _)).trans (Category.id_comp _)
  rw [hleft, LX.map_comp, ← Category.assoc]
  have hn := SX.adjunction.unit_naturality (D.limit.hom.app N)
  change SX.adjunction.unit.app (F.obj (LY.obj N)) ≫
      LX.map (SX.reduction.map (D.limit.hom.app N)) =
    D.limit.hom.app N ≫ SX.adjunction.unit.app (LX.obj (G.obj N)) at hn
  rw [hn]
  have ht := SX.adjunction.right_triangle_components (G.obj N)
  change SX.adjunction.unit.app (LX.obj (G.obj N)) ≫
    LX.map (SX.adjunction.counit.app (G.obj N)) = 𝟙 _ at ht
  rw [Category.assoc, ht]
  exact (Category.comp_id (D.limit.hom.app N)).symm

private theorem podRoosBoundary_reindex (D : PodCompletionReindex l E g) :
    PodCompletionReindex.RoosBoundary l E g D := by
  intro C
  let F := isoReductionIntegralComplex l E g
  have hy (n : ℕ) := (towerTransitionEndomorphism_eq_iff
    (K := fun n : ℕ ↦ C.obj (op n)) (integralOperationsTowerStep C) _).1 rfl n
  have hx (n : ℕ) := (towerTransitionEndomorphism_eq_iff
    (K := fun n : ℕ ↦ ((podReindexTower l E g).obj C).obj (op n))
    (integralOperationsTowerStep ((podReindexTower l E g).obj C)) _).1 rfl n
  apply Pi.hom_ext
  intro n
  change F.map (podRoosBoundary C) ≫ podReindexProduct l E g C ≫ Pi.π _ n =
    podReindexProduct l E g C ≫ podRoosBoundary ((podReindexTower l E g).obj C) ≫
      Pi.π _ n
  dsimp only [podReindexProduct]
  rw [Pi.lift_comp_π, ← F.map_comp, hy, F.map_sub, F.map_comp, hx,
    Preadditive.comp_sub, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
  rfl

/-- The ambient reduction and completion assertion with independent scheme and coefficient
universes. Completeness is required only to invert the specified unit and pullback map.
Source: blueprint theorem-poincare-duality-frobenius--2, proof Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-completion-unit-tensor).

Proof: the projection-normalized coefficient isomorphisms give exact inverse equivalences
on strict systems. On a single flat-term K-flat representative the quotient comparison
sends p tensor b to Fp tensor Fb, compatibly with each quotient transition. Projection-defined
product comparison commutes with 1-s, and its diagonal map on both shifted-cone coordinates
is the normalized total-derived-limit comparison. Derive the ordinary tensor/limit Hom
bijection on simultaneous K-flat and K-injective representatives; its reindexing identity
identifies the actual unit and counit as whole-system maps. For E=E the finite-free scalar
comparison identifies the completion augmentation with this unit. Normalized reconstruction
makes it invertible on every derived-complete input. Composing its inverse-image map with
the specified limit comparison and pullback realization gives the displayed isomorphism.
The diagonal cone map commutes with signed shifts because the second shift coordinate is
multiplied by (-1)^r. These are node proof steps 1--5 and the shift calculation of step 8. -/
theorem podReindexingCompletionUnit {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ D : PodCompletionReindex l E g,
      PodCompletionReindex.Laws l E g D ∧
      ∀ K : DerivedCategory (scalarReductionSource l E Y),
        IntegralOnSlice.IsComplete l E Y none K →
          IsIso ((podOrdinaryToCompleted l E g D).app K) := by
  obtain ⟨SY, hSY⟩ := podReindexingSignedRoosShift (A := scalarReductionSource l E Y)
  obtain ⟨SX, hSX⟩ := podReindexingSignedRoosShift (A := scalarReductionSource l E X)
  obtain ⟨S, hS⟩ := podReindexingStrictComparisons l E g SY SX hSY hSX
  obtain ⟨β, hgen, _, htransition, _, _⟩ := isomorphismReductionTower l E g
  obtain ⟨CY, hCY⟩ := podReindexingCompletionNormalization l E Y
  obtain ⟨CX, hCX⟩ := podReindexingCompletionNormalization l E X
  obtain ⟨R, hR⟩ := podReindexingDerivedComparisons l E g SY SX S hS β hgen htransition CY CX
  rcases hS with ⟨hfst, hsnd, hnat, hshift, hres⟩
  rcases hR with ⟨hreduction, hprojection, hunit, hfinite,
    hlimit, hpullback⟩
  let D := R.assemble l E g SY SX S β CY CX
  refine ⟨D, ?_, ?_⟩
  · exact ⟨⟨hCY, hCX⟩, hreduction, hprojection, hunit, podCounit_of_unit l E g D hunit,
      podCompleteUnit l E g D,
      hgen, htransition, hfinite, podRoosBoundary_reindex l E g D, hfst, hsnd, hnat,
      hSY, hSX, hshift, hres, hlimit, hpullback⟩
  · exact podOrdinaryToCompleted_isIso l E g D (podCompleteUnit l E g D)

/-- Projection-normalized ordinary reindexing commutes with completion and completed tensor.

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941
(blueprint: lem-pod-reindexing-completion-unit-tensor).

Proof: use the exact sectionwise coefficient-module equivalences at R and every B_n.
Their projection squares induce an exact equivalence on whole semilinear systems;
its inverse transports acyclic complexes, hence the defining null-homotopies of
K-injectivity. On simultaneous flat-term K-flat resolutions send p tensor b to
Fp tensor Fb. The same formula commutes with each quotient arrow and every chain
map, so it localizes to the specified coherent reduction comparison. Reindex
countable products by their projections. This commutes with the shift operator s,
so the diagonal map on the two product coordinates is a map of Cone(1-s)[-1].
Reverse relabelling is its inverse. The K-injective limit-to-Roos comparison
identifies this map with the total derived limit comparison. Transport the
ordinary tensor/restriction adjunction before deriving: its generator formula
identifies both unit and counit, including their whole-system maps. The original
completion augmentation is the identity-scalar normalization of the finite-free
scalar comparison. Normalized reconstruction therefore makes its actual unit
invertible precisely on complete inputs. The specified F(unit), limit comparison,
and inverse pullback realization give the asserted ordinary-to-completed map.
For tensor, reindex each summand of simultaneous flat K-flat total tensors. The
formula commutes with the signed total differential and quotient maps. Applying
the same two-coordinate Roos map gives the displayed tensor comparison and its
reverse-reindexing inverse. Its finite generator formula is the prescribed finite
pullback/tensor comparison; the normalized whole-system reduction square then
identifies it with the prescribed integral comparison. Naturality descends along
roofs. On three homogeneous factors both reassociation routes agree, and both
symmetry routes give (-1)^(pq) Fy tensor Fx. Identity and composition are literal
successive relabellings with the canonical coefficient/projection transports.
The shifted second cone coordinate has (-1)^r, giving the two displayed signed
shift equations. Finally apply completed-operation substitution to these same
normalized primitives: its coherent counit formulas retain all quotient arrows,
and its structural squares give the functorial realizations of these equations.
This argument uses no boundedness and applies also to empty schemes. -/
theorem podReindexingCompletionUnitTensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃ A : PodReindexFamily l E,
      A.Relabelling l E ∧ A.Identity l E ∧ A.Composition l E ∧
      (∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
        [∀ v : V, Invertible (l : V.residueField v)]
        [∀ w : W, Invertible (l : W.residueField w)],
        PodCompletionReindex.Laws l E f (A.completion f) ∧
        (∀ K : DerivedCategory (scalarReductionSource l E W),
          IntegralOnSlice.IsComplete l E W none K →
            IsIso ((podOrdinaryToCompleted l E f (A.completion f)).app K)) ∧
        (∀ K : sfIntegralConstructibleCategory l E W,
          IsIso ((podOrdinaryToCompleted l E f (A.completion f)).app K.obj)) ∧
        PodCompletedTensorReindex.Laws l E f (A.completion f) (A.tensor f) ∧
        A.TensorConstraints l E f) ∧
      (∃ SY : PodTensorSignedShift l E Y, ∃ SX : PodTensorSignedShift l E X,
        PodReindexSignedShifts l E g (A.completion g) (A.tensor g) SY SX) ∧
      (∀ (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
        (ι : E →ₐ[ℚ_[l]] L),
        ∃ D' : PodCompletionReindex l L g,
        ∃ T' : PodCompletedTensorReindex l L g D',
        ∃ S : PodReindexCoefficientTransition l E L ι g (A.completion g) D',
          PodCompletionReindex.Laws l L g D' ∧
          PodCompletedTensorReindex.Laws l L g D' T' ∧
          S.Laws l E L ι g (A.completion g) D' (A.tensor g) T') ∧
      PodReindexSubstitution l E g (A.completion g) (A.tensor g) := by
  classical
  have hcompletion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      ∃ D : PodCompletionReindex l E f, PodCompletionReindex.Laws l E f D := by
    intro V W f _ _ _
    obtain ⟨D, hD, _⟩ := podReindexingCompletionUnit l E f
    exact ⟨D, hD⟩
  let completion : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)], PodCompletionReindex l E f :=
    fun f ↦ (hcompletion f).choose
  have hD : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletionReindex.Laws l E f (completion f) :=
    fun f ↦ (hcompletion f).choose_spec
  let tensor : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex l E f (completion f) :=
    fun f ↦ (podReindexingTensorConstruction l E f (completion f) (hD f)).choose
  have hT : ∀ {V W : Scheme.{u}} (f : V ⟶ W) [IsIso f]
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)],
      PodCompletedTensorReindex.Laws l E f (completion f) (tensor f) :=
    fun f ↦ (podReindexingTensorConstruction l E f (completion f) (hD f)).choose_spec
  obtain ⟨identity, composition, hR, hI, hC, hTC⟩ :=
    podReindexingTensorFamilyCoherence l E completion tensor hD hT
  let A : PodReindexFamily l E := ⟨completion, tensor, identity, composition⟩
  refine ⟨A, hR, hI, hC, ?_, ?_, ?_, ?_⟩
  · intro V W f _ _ _
    refine ⟨hD f, ?_, ?_, hT f, hTC f⟩
    · exact podOrdinaryToCompleted_isIso l E f (completion f) (podCompleteUnit l E f _)
    · intro K
      obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
      let : Fact p.Prime := ⟨hp⟩
      let Δ : FiniteFieldDatum.{0} := {
        p := p, a := 1, q := p, prime := hp, exponent_pos := le_refl 1,
        cardinality_eq := (pow_one p).symm, k₀ := ZMod p,
        card_base := by simp [Nat.card_eq_fintype_card]
        k := AlgebraicClosure (ZMod p) }
      have hlp : l ≠ Δ.p := by change l ≠ p; omega
      have hK : IntegralOnSlice.IsComplete l E W none K.obj :=
        ⟨Δ, hlp, (sfDerivedComplete_iff_legacy l E W Δ hlp K.obj).mp K.property.1⟩
      exact podOrdinaryToCompleted_isIso l E f (completion f)
        (podCompleteUnit l E f _) K.obj hK
  · exact podReindexingTensorSignedShifts l E g (completion g) (hD g) (tensor g) (hT g)
  · intro L _ _ _ ι
    obtain ⟨D', hD', _⟩ := podReindexingCompletionUnit l L g
    obtain ⟨T', hT'⟩ := podReindexingTensorConstruction l L g D' hD'
    obtain ⟨S, hS⟩ := podReindexingTensorCoefficientTransition l E g (completion g)
      (hD g) (tensor g) (hT g) L ι D' hD' T' hT'
    exact ⟨D', T', S, hD', hT', hS⟩
  · exact podReindexingTensorSubstitution l E g (completion g) (hD g) (tensor g) (hT g)

end WeilConjectures
