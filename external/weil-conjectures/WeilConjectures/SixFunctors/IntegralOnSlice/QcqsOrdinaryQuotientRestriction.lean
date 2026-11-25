/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.OrdinaryQuotientModuleComparison
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

/-! # Augmented strict quotient towers under qcqs restriction

Source: Stacks Tags 06YY and 07A4. -/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
attribute [local irreducible] ordinaryPull reductionWitness

section Assembly
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (f : X ⟶ Y)
  (e : ∀ n : ℕ, ordinaryQuotientModule l E Y n ⋙ ordinaryPull l E f ≅
    ordinaryPull l E f ⋙ ordinaryQuotientModule l E X n)
  (he : ∀ (n : ℕ) (M : Mod l E Y none) (V : Y.ProEt)
    (a : (finite l E Y none n).obj.obj (op V)) (x : M.val.obj (op V)),
    ((e n).hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
      (((ordinaryAdjunction l E f).unit.app
        ((ordinaryQuotientModule l E Y n).obj M)).val.app (op V)
          (generator l E Y none n M (op V) a x)) =
      generator l E X none n ((ordinaryPull l E f).obj M)
        (op ((proEtaleBaseChange f).obj V))
        ((ordinaryFiniteRingMap l E f n).hom.app (op V) a)
        (((ordinaryAdjunction l E f).unit.app M).val.app (op V) x))

private def quotientLevelIso (n : ℕ) :
    level l E Y none n ⋙ ordinaryComplexPull l E f ≅
      ordinaryComplexPull l E f ⋙ level l E X none n :=
  NatIso.mapHomologicalComplex (e n) (.up ℤ)

private theorem finiteCoefficientMap_naturality
    {A B : CommRingCat.{max u (t + 1)}} (q : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map q ≫
        coefficientProEtaleDirectRingMap f B =
      coefficientProEtaleDirectRingMap f A ≫
        ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).map
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map q) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  change (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)}).homEquiv _ _
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map
      ((Functor.const _).map q) ≫ _) = _
  erw [Adjunction.homEquiv_naturality_left
    (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)})
    ((Functor.const Y.ProEtᵒᵖ).map q) (coefficientProEtaleDirectRingMap f B),
    Adjunction.homEquiv_naturality_right
      (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{max u (t + 1)})
      (coefficientProEtaleDirectRingMap f A)
      (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map q))]
  unfold coefficientProEtaleDirectRingMap
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congrArg (fun z ↦ z.app ((proEtaleBaseChange f).op.obj V))
    ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{max u (t + 1)}).unit.naturality
      ((Functor.const _).map q))

private theorem quotientModule_hom_ext (n : ℕ) (M N : Mod l E Y none)
    (a b : (ordinaryQuotientModule l E Y n).obj M ⟶ N)
    (h : ∀ V s x, a.val.app V (generator l E Y none n M V s x) =
      b.val.app V (generator l E Y none n M V s x)) : a = b :=
  SheafOfModules.UnrestrictedTowerProof.identified_hom_ext
    (projection l E Y none n) M
    (reduction l E Y none n)
    (reduction_obj l E Y none n) N a b
      (fun V s x ↦ by
        convert h V s x using 1 <;> rfl)

private theorem finiteRingMap_step (n : ℕ) (V : Y.ProEt)
    (a : (finite l E Y none (n + 1)).obj.obj (op V)) :
    (ordinaryFiniteRingMap l E f n).hom.app (op V)
        ((rho l E Y none n).hom.app (op V) a) =
      (rho l E X none n).hom.app (op ((proEtaleBaseChange f).obj V))
        ((ordinaryFiniteRingMap l E f (n + 1)).hom.app (op V) a) := by
  let q := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
  exact congrArg (fun k ↦ k.hom.app (op V) a) (finiteCoefficientMap_naturality f q)

include e he

private theorem quotientLevelIso_transition (n : ℕ) :
    Functor.whiskerRight (transition l E Y none n) (ordinaryComplexPull l E f) ≫
        (quotientLevelIso l E f e n).hom =
      (quotientLevelIso l E f e (n + 1)).hom ≫
        Functor.whiskerLeft (ordinaryComplexPull l E f) (transition l E X none n) := by
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro j
  apply ((ordinaryAdjunction l E f).homEquiv _ _).injective
  apply quotientModule_hom_ext l E (n + 1) (P.X j)
  intro V a x
  let W : (Site X none)ᵒᵖ := op ((proEtaleBaseChange f).obj V.unop)
  let b := ((transition l E Y none n).app P).f j
  have hu := congrArg (fun k ↦ k.val.app V
    (generator l E Y none (n + 1) (P.X j) V a x))
      ((ordinaryAdjunction l E f).unit.naturality b)
  have hy := (transition_existsUnique l E Y none n).exists.choose_spec P j V a x
  have hx := (transition_existsUnique l E X none n).exists.choose_spec
    ((ordinaryComplexPull l E f).obj P) j W
    ((ordinaryFiniteRingMap l E f (n + 1)).hom.app V a)
    (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)
  change ((e n).hom.app (P.X j)).val.app W
      (((ordinaryPull l E f).map b).val.app W
        (((ordinaryAdjunction l E f).unit.app
          ((ordinaryQuotientModule l E Y (n + 1)).obj (P.X j))).val.app V
            (generator l E Y none (n + 1) (P.X j) V a x))) =
    (((transition l E X none n).app ((ordinaryComplexPull l E f).obj P)).f j).val.app W
      (((e (n + 1)).hom.app (P.X j)).val.app W
        (((ordinaryAdjunction l E f).unit.app
          ((ordinaryQuotientModule l E Y (n + 1)).obj (P.X j))).val.app V
            (generator l E Y none (n + 1) (P.X j) V a x)))
  change (((ordinaryAdjunction l E f).unit.app
      ((ordinaryQuotientModule l E Y n).obj (P.X j))).val.app V
        (b.val.app V (generator l E Y none (n + 1) (P.X j) V a x))) =
    ((ordinaryPull l E f).map b).val.app W
      (((ordinaryAdjunction l E f).unit.app
        ((ordinaryQuotientModule l E Y (n + 1)).obj (P.X j))).val.app V
          (generator l E Y none (n + 1) (P.X j) V a x)) at hu
  rw [← hu]
  change b.val.app V (generator l E Y none (n + 1) (P.X j) V a x) = _ at hy
  change ((((transition l E X none n).app ((ordinaryComplexPull l E f).obj P)).f j).val.app W
      (generator l E X none (n + 1) ((ordinaryPull l E f).obj (P.X j)) W
        ((ordinaryFiniteRingMap l E f (n + 1)).hom.app V a)
        (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x))) =
    generator l E X none n ((ordinaryPull l E f).obj (P.X j)) W
      ((rho l E X none n).hom.app W
        ((ordinaryFiniteRingMap l E f (n + 1)).hom.app V a))
      (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x) at hx
  erw [hy, he n, he (n + 1)]
  exact (congrArg (fun z ↦ generator l E X none n ((ordinaryPull l E f).obj (P.X j))
    W z (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x))
      (finiteRingMap_step l E f n V.unop a)).trans hx.symm

private theorem quotientLevelIso_augmentation (n : ℕ) (P : Cx l E Y none) :
    (ordinaryComplexPull l E f).map (((augmentation l E Y none).app P).app (op n)) ≫
        (quotientLevelIso l E f e n).hom.app P =
      ((augmentation l E X none).app ((ordinaryComplexPull l E f).obj P)).app (op n) := by
  apply HomologicalComplex.hom_ext
  intro j
  apply ((ordinaryAdjunction l E f).homEquiv _ _).injective
  ext V x
  let W : (Site X none)ᵒᵖ := op ((proEtaleBaseChange f).obj V.unop)
  let b := (((augmentation l E Y none).app P).app (op n)).f j
  have hu := congrArg (fun k ↦ k.val.app V x)
    ((ordinaryAdjunction l E f).unit.naturality b)
  have hy := (augmentation_existsUnique l E Y none).exists.choose_spec P n j V x
  have hx := (augmentation_existsUnique l E X none).exists.choose_spec
    ((ordinaryComplexPull l E f).obj P) n j W
    (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)
  change ((e n).hom.app (P.X j)).val.app W
      (((ordinaryPull l E f).map b).val.app W
        (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)) =
    ((((augmentation l E X none).app
      ((ordinaryComplexPull l E f).obj P)).app (op n)).f j).val.app W
        (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)
  change (((ordinaryAdjunction l E f).unit.app
      ((ordinaryQuotientModule l E Y n).obj (P.X j))).val.app V (b.val.app V x)) =
    ((ordinaryPull l E f).map b).val.app W
      (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x) at hu
  change b.val.app V x = _ at hy
  erw [← hu, hy, he n]
  change (((((augmentation l E X none).app
      ((ordinaryComplexPull l E f).obj P)).app (op n)).f j).val.app W
        (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)) =
    generator l E X none n ((ordinaryPull l E f).obj (P.X j)) W 1
      (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x) at hx
  have h1 : (ordinaryFiniteRingMap l E f n).hom.app V 1 = 1 := map_one _
  exact (congrArg (fun a ↦ generator l E X none n ((ordinaryPull l E f).obj (P.X j)) W a
    (((ordinaryAdjunction l E f).unit.app (P.X j)).val.app V x)) h1).trans hx.symm

private def quotientTowerIso :
    tower l E Y none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (Cx l E Y none) (Cx l E X none)).obj
          (ordinaryComplexPull l E f) ≅
      ordinaryComplexPull l E f ⋙ tower l E X none := by
  let α (P : Cx l E Y none) :
      ((tower l E Y none).obj P ⋙ ordinaryComplexPull l E f) ⟶
        (tower l E X none).obj ((ordinaryComplexPull l E f).obj P) :=
    NatTrans.ofOpSequence (fun n ↦ (quotientLevelIso l E f e n).hom.app P) (by
      intro n
      change (ordinaryComplexPull l E f).map
          (((Functor.ofOpSequence (transition l E Y none)).map
            (homOfLE (Nat.le_succ n)).op).app P) ≫ _ =
        _ ≫ ((Functor.ofOpSequence (transition l E X none)).map
          (homOfLE (Nat.le_succ n)).op).app ((ordinaryComplexPull l E f).obj P)
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact NatTrans.congr_app (quotientLevelIso_transition l E f e he n) P)
  have hα (P) : IsIso (α P) := by
    have hn (n : ℕᵒᵖ) : IsIso ((α P).app n) := by
      change IsIso ((quotientLevelIso l E f e n.unop).hom.app P)
      infer_instance
    exact NatIso.isIso_of_isIso_app (α P)
  exact NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (α P) (hα P)) (by
    intro P Q a
    apply NatTrans.ext
    funext n
    exact (quotientLevelIso l E f e n.unop).hom.naturality a)

end Assembly

@[expose] public section

/-- Pullback commutes with the strict finite quotient tower and its augmentation.

Source: Stacks Tags 06YY and 07A4; Bhatt--Scholze Lemma 6.5.8(1).
(blueprint: lem-fix-qcqs-ordinary-quotient-restriction).
Proof: identify the pullback of each finite constant coefficient sheaf with the
same coefficient sheaf on S by its constant-section map. The completed coefficient
map commutes with the projections to these sheaves by adjunction and the defining
projection equations for ordinaryCompletedRingMap. Tensor base change therefore
identifies pullback of reduction at n with reduction of pullback at n. The natural
isomorphism sends the generator m tensor a to the pulled-back m tensor the same a.
The transition from n+1 to n has the same formula on both sides, because the
constant-section maps commute with quotient homomorphisms. The generators determine
maps after sheafification, so these isomorphisms form a map of strict towers.
Apply degreewise to complexes; naturality preserves every differential. The
augmentation generator is m tensor 1, which the isomorphism preserves, giving the
stated augmentation equality. The argument also covers zero modules, n=0 (the
first quotient, at exponent one), and the empty scheme. This is an ordinary
chain-level tensor comparison and uses no derived descent or Roos construction. -/
theorem qcqsOrdinaryQuotientRestriction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace T] [QuasiSeparatedSpace T]
    (s : S ⟶ V) (i : V ⟶ T) [WeaklyEtale s] [IsImmersion i] :
    let r := s ≫ i
    ∃ (τ : tower l E T none ⋙
          (Functor.whiskeringRight ℕᵒᵖ (Cx l E T none) (Cx l E S none)).obj
            (ordinaryComplexPull l E r) ≅
          ordinaryComplexPull l E r ⋙ tower l E S none),
        (∀ (P : Cx l E T none) (n : ℕ),
          (ordinaryComplexPull l E r).map (((augmentation l E T none).app P).app (op n)) ≫
              (τ.hom.app P).app (op n) =
            ((augmentation l E S none).app ((ordinaryComplexPull l E r).obj P)).app (op n)) := by
  have : IsIso (ordinaryCoefficientMap l E (s ≫ i)) :=
    (qcqsOrdinaryRestrictionExact l E s i).2
  choose e he using fun n ↦ (ordinaryQuotientModuleComparison l E (s ≫ i) n).exists
  refine ⟨quotientTowerIso l E (s ≫ i) e he, ?_⟩
  intro P n
  exact quotientLevelIso_augmentation l E (s ≫ i) e he n P

end
end WeilConjectures.IntegralOnSlice
end
