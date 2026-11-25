/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData

/-! # Coordinates of the transported ordinary completion chain

Source: Stacks Tags 08TC and 0941; Bhatt--Scholze Lemma 6.5.9(4).
(blueprint: lem-weil-pbc-integral-completion-transport-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private abbrev boundary {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
    (integralOperationsTowerStep C)

/-- Coefficient transport takes the ordinary completion chain to the actual
quotient augmentation in the first coordinate and zero in the second.

Source: Stacks Tags 08TC and 0941; Bhatt--Scholze Lemma 6.5.9(4).
(blueprint: lem-weil-pbc-integral-completion-transport-coordinates).

Proof: define c by composing the inverse module identification, the transported
ordinary chain and z. Cancel the module identification for the first equality.
For each first product projection, the coordinate identity of z reduces the
composite to scalar restriction of the ordinary chain followed by its first
projection and the inverse component of t. The mapping-cocone lift formula and
product lift formula identify this with the transported quotient augmentation.
The assumed augmentation equation and the two inverse identities give the actual
augmentation. For the shifted coordinate use product extensionality, the second
coordinate identity of z, and the zero shifted coordinate of the ordinary lift.
Scalar restriction preserves zero. No resolution or derived-unit formula enters.
The argument applies to zero complexes and empty schemes. -/
theorem pbc_integral_completion_transport_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (a : ordinaryIntegralModulePull l E h ⋙ pbcIntegralTransportModules U l E ≅
      pbcIntegralTransportModules T l E ⋙ completedModulePullback h (pbcIntegralDatum l E))
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (t : (pbcIntegralActualTower l E h P).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E h).obj P ⋙ pbcIntegralTransportComplex U l E)
    (z : (pbcIntegralTransportComplex U l E).obj
      ((integralOperationsPullbackComplexFunctor l E h).obj P) ≅
      integralOperationsRoos (pbcIntegralActualTower l E h P).asFunctor)
    (ht : ∀ n : ℕ, (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app P ≫
      pbcIntegralActualTowerAugmentation l E h P n ≫ t.hom.app (op n) =
      (pbcIntegralTransportComplex U l E).map
        (((ordinaryIntegralQuotientAugmentation l E h).app P).app (op n)))
    (hz : PbcIntegralRoosTransportCoordinates U l E
      (pbcIntegralActualTower l E h P).asFunctor
      ((integralOperationsPullbackTowerFunctor l E h).obj P) t z) :
    let G := pbcIntegralTransportComplex U l E
    let j := (NatIso.mapHomologicalComplex a (.up ℤ)).app P
    let c := j.inv ≫ G.map (ordinaryIntegralCompletionChain l E h P) ≫ z.hom
    (j.hom ≫ c = G.map (ordinaryIntegralCompletionChain l E h P) ≫ z.hom) ∧
    (∀ (n : ℕ) (i : ℤ),
      c.f i ≫ (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism
        (K := fun m : ℕ ↦ (pbcIntegralActualTower l E h P).asFunctor.obj (op m))
        (integralOperationsTowerStep (pbcIntegralActualTower l E h P).asFunctor))).f i ≫
        (Pi.π (fun m : ℕ ↦
          (pbcIntegralActualTower l E h P).asFunctor.obj (op m)) n).f i =
        (pbcIntegralActualTowerAugmentation l E h P n).f i) ∧
    (∀ (i j' : ℤ) (hij : i + -1 = j'),
      c.f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism
        (K := fun m : ℕ ↦ (pbcIntegralActualTower l E h P).asFunctor.obj (op m))
        (integralOperationsTowerStep (pbcIntegralActualTower l E h P).asFunctor))).v
          i j' hij = 0) := by
  let F := pbcIntegralTransportModules U l E
  let G := pbcIntegralTransportComplex U l E
  let j := (NatIso.mapHomologicalComplex a (.up ℤ)).app P
  let c := j.inv ≫ G.map (ordinaryIntegralCompletionChain l E h P) ≫ z.hom
  have ht' (n : ℕ) :
      G.map (((ordinaryIntegralQuotientAugmentation l E h).app P).app (op n)) ≫
          t.inv.app (op n) =
        j.hom ≫ pbcIntegralActualTowerAugmentation l E h P n := by
    rw [← ht n]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    rfl
  have hc₁ (n : ℕ) (i : ℤ) :
      c.f i ≫ (CochainComplex.mappingCocone.fst
        (boundary (pbcIntegralActualTower l E h P).asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦
          (pbcIntegralActualTower l E h P).asFunctor.obj (op m)) n).f i =
        (pbcIntegralActualTowerAugmentation l E h P n).f i := by
    have hz₁ := hz.1 n i
    dsimp only [c]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [hz₁]
    change j.inv.f i ≫ F.map ((ordinaryIntegralCompletionChain l E h P).f i) ≫
      F.map _ ≫ _ = _
    rw [← F.map_comp_assoc]
    have hα : (ordinaryIntegralCompletionChain l E h P).f i ≫
        (CochainComplex.mappingCocone.fst
          (boundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).f i ≫
        (Pi.π (fun m : ℕ ↦
          ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n).f i =
      (((ordinaryIntegralQuotientAugmentation l E h).app P).app (op n)).f i := by
      unfold ordinaryIntegralCompletionChain
      rw [← Category.assoc, CochainComplex.mappingCocone.lift_f_fst_f]
      have hp := Pi.lift_comp_π (fun m : ℕ ↦
        ((ordinaryIntegralQuotientAugmentation l E h).app P).app (op m)) n
      exact congrArg (fun f ↦ f.f i) hp
    rw [hα]
    have hh := congrArg (fun f ↦ f.f i) (ht' n)
    change F.map _ ≫ _ = j.hom.f i ≫ _ at hh
    rw [hh, ← Category.assoc]
    have hj := congrArg (fun f ↦ f.f i) j.inv_hom_id
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.id_comp]
      using congrArg (fun f ↦ f ≫ (pbcIntegralActualTowerAugmentation l E h P n).f i) hj
  have hc₂ (i j' : ℤ) (hij : i + -1 = j') :
      c.f i ≫ (CochainComplex.mappingCocone.snd
        (boundary (pbcIntegralActualTower l E h P).asFunctor)).v i j' hij = 0 := by
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval _ (.up ℤ) j')
      (fun n : ℕ ↦ (pbcIntegralActualTower l E h P).asFunctor.obj (op n))).hom_ext
    rintro ⟨n⟩
    simp only [Fan.mk_π_app, HomologicalComplex.eval_map, zero_comp]
    dsimp only [c]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [hz.2 n i j' hij]
    change j.inv.f i ≫ F.map ((ordinaryIntegralCompletionChain l E h P).f i) ≫
      F.map _ ≫ _ = 0
    rw [← F.map_comp_assoc]
    have hα : (ordinaryIntegralCompletionChain l E h P).f i ≫
        (CochainComplex.mappingCocone.snd
          (boundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
            i j' hij = 0 := by
      unfold ordinaryIntegralCompletionChain
      exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ i j' hij
    have hα' := congrArg (fun f ↦ f ≫
      (Pi.π (fun m : ℕ ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op m)) n).f j') hα
    simp only [Category.assoc, zero_comp] at hα'
    rw [hα', F.map_zero, zero_comp, comp_zero]
  have hjc : j.hom ≫ c =
      G.map (ordinaryIntegralCompletionChain l E h P) ≫ z.hom := by
    dsimp only [c]
    simp only [← Category.assoc, j.hom_inv_id, Category.id_comp]
  exact ⟨hjc, hc₁, hc₂⟩

end WeilConjectures
