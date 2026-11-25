/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbRootTowerPullbackCoherence
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement

/-! # Completed root scalars in the integral tensor

Source: Stacks Project, `sites-modules.tex`, Tags 03EK and 03EL.
(blueprint: new-weil-frobenius-integral-root-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] MorphismProperty.Over.pullback constantSheaf Padic
attribute [local instance_reducible] PurCompactSupport.completed

private abbrev zlDirectCone
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Cone (purTwistZlTower X l ⋙ proEtaleSheafDirectImage g CommRingCat.{u + 1}) where
  pt := purTwistZlCompletion Y l
  π := NatTrans.ofOpSequence
    (fun n ↦ purTwistZlProjection Y l n ≫
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) (by
      intro n
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      simp only [Functor.comp_map, purTwistZlTower, purTwistZlTowerOfUniverses,
        Functor.ofOpSequence_map_homOfLE_succ]
      change purTwistZlProjection Y l n ≫ _ =
        (purTwistZlProjection Y l (n + 1) ≫ _) ≫
          (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
            (purTwistFiniteTransition X l n)
      rw [Category.assoc]
      dsimp only [purTwistFiniteTransition, purTwistFiniteTransitionOfUniverses]
      rw [← AlgebraicGeometry.Scheme.constant_naturality]
      have hw := limit.w (purTwistZlTower Y l) (homOfLE (Nat.le_succ n)).op
      simp only [purTwistZlTower, purTwistZlTowerOfUniverses,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      exact (congrArg (fun k ↦ k ≫ proEtaleConstantDirectImageMap g
        CommRingCat.{u + 1} _) hw).symm)

private def zlDirect
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purTwistZlCompletion Y l ⟶
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj (purTwistZlCompletion X l) :=
  letI := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).isRightAdjoint
  limit.lift _ (zlDirectCone l g) ≫
    inv (limit.post (purTwistZlTower X l)
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}))

private theorem zlDirect_projection
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    zlDirect l g ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (purTwistZlProjection X l n) =
      purTwistZlProjection Y l n ≫
        proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) := by
  let := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).isRightAdjoint
  unfold zlDirect
  dsimp only [purTwistZlProjection, purTwistZlProjectionOfUniverses]
  rw [Category.assoc, ← limit.post_π, IsIso.inv_hom_id_assoc, limit.lift_π]
  rfl

private theorem root_completed_linear
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEtᵒᵖ)
    (a : (purTwistZlCompletion Y l).obj.obj U)
    (x : (purTwistZlOne Y l).obj.obj U) :
    (AlgebraicGeometry.Scheme.root_direct l g).hom.app U
        (@SMul.smul _ _ (purTwistZlAction Y l U).toSMul a x) =
      @SMul.smul _ _
        (purTwistZlAction X l ((proEtaleBaseChange g).op.obj U)).toSMul
        ((zlDirect l g).hom.app U a)
        ((AlgebraicGeometry.Scheme.root_direct l g).hom.app U x) := by
  apply AlgebraicGeometry.Scheme.root_section_ext l
  intro n
  have hy := (purTwistZlAction_existsUnique Y l).exists.choose_spec.2 n U a x
  have hx := (purTwistZlAction_existsUnique X l).exists.choose_spec.2 n
    ((proEtaleBaseChange g).op.obj U) ((zlDirect l g).hom.app U a)
    ((AlgebraicGeometry.Scheme.root_direct l g).hom.app U x)
  erw [AlgebraicGeometry.Scheme.root_direct_project_value, hy,
    AlgebraicGeometry.Scheme.root_direct_linear, hx,
    AlgebraicGeometry.Scheme.root_direct_project_value]
  congr 1
  exact (congrArg (fun k ↦ k.hom.app U a) (zlDirect_projection l g n)).symm

private theorem completedDirect_hom_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {T : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {a b : T ⟶ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (completedIntegralCommRingSheafUnrestricted l E X)}
    (h : ∀ n, a ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (completedIntegralCommRingProjectionUnrestricted l E X n) =
      b ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (completedIntegralCommRingProjectionUnrestricted l E X n)) : a = b := by
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  apply (adj.homEquiv _ _).symm.injective
  let H := sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply H.map_injective
  apply limit.hom_ext
  intro n
  have hn := congrArg (adj.homEquiv _ _).symm (h n.unop)
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_right_symm] at hn
  exact congrArg H.map hn

private theorem completedScalar_projection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (n k : ℕ)
    (q : ZMod (l ^ (k + 1)) →+* Padic.coefficientExtensionRing l E (n + 1))
    (hq : ∀ z : ℤ_[l], q (PadicInt.toZModPow (k + 1) z) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (purTwistIntegersMap l E z)) :
    purTwistCompletedScalarMap S l E ≫ completedIntegralCommRingProjectionUnrestricted
        l E S n =
      purTwistZlProjection S l k ≫
        (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
            (q.comp ULift.ringEquiv.toRingHom))) := by
  obtain ⟨m, q', hq', hm⟩ :=
    (purTwistCompletedScalarMap_existsUnique S l E).exists.choose_spec n
  change purTwistCompletedScalarMap S l E ≫ _ = _ at hm
  rw [hm]
  apply AlgebraicGeometry.Scheme.purTwistZlFiniteFactor_ext
  dsimp [purTwistZlReductionOfUniverses]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext z
  exact (hq' z.down).trans (hq z.down).symm

private theorem completedScalar_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purTwistCompletedScalarMap Y l E ≫ sfCompletedCoefficientMap l E g =
      zlDirect l g ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        (purTwistCompletedScalarMap X l E) := by
  apply completedDirect_hom_ext l E g
  intro n
  obtain ⟨k, q, hq, hy⟩ :=
    (purTwistCompletedScalarMap_existsUnique Y l E).exists.choose_spec n
  change purTwistCompletedScalarMap Y l E ≫ _ = _ at hy
  have hx := completedScalar_projection l E X n k q hq
  erw [Category.assoc, (sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec,
    ← Category.assoc, hy]
  rw [Category.assoc, AlgebraicGeometry.Scheme.constant_naturality]
  rw [← Category.assoc, ← zlDirect_projection]
  rw [Category.assoc, ← Functor.map_comp, ← hx, Functor.map_comp, ← Category.assoc]

/-- Compatibility of root-limit scalars after the integral tensor inclusion.

Source: the finite scalar clause of `proEtaleRootsOfUnityInverseImageIso`, the
coordinate characterization of `purTwistZlAction_existsUnique`, and Stacks Project,
`sites-modules.tex`, tensor-product construction (Tags 03EK and 03EL).
Proof: form the direct-image map of completed Z_l rings from the compatible
constant Z/l^(n+1) comparisons. Project the adjunct of r to level n. Naturality of
the adjunction unit and of the limit comparison identifies this projection with
the adjunct of the finite root comparison. Its finite scalar formula, together
with the coordinate definition of the Z_l action, proves semilinearity of the root
limit map, since its projections are jointly injective. The completed coefficient
map commutes with the map from completed Z_l: after each integral coefficient
projection, both composites factor through the same finite Z/l^k quotient and
have the same constant residues. The uniqueness specification of the completed
scalar map proves this assertion also for ramified E. Apply the normalization
formula for the completed action on an integral pure tensor on X and substitute
the root-limit semilinearity just proved. This gives the displayed equality.
The argument uses only finite projection identities and includes the empty site.
(blueprint: new-weil-frobenius-integral-root-scalar). -/
theorem frobeniusIntegralRootScalar
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose)) :
    ∀ (V : Y.ProEt) (a : (purTwistZlCompletion Y l).obj.obj (op V))
      (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (x : (purTwistZlOne Y l).obj.obj (op V)),
      purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V))
        ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
              (op V) b)
        (r.hom.app (op ((proEtaleBaseChange g).obj V))
              (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
                (purTwistZlOne Y l)).hom.app (op V)
                  (@SMul.smul _ _ (purTwistZlAction Y l (op V)).toSMul a x))) =
      @SMul.smul _ _
        (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
        ((sfCompletedCoefficientMap l E g).hom.app (op V)
          ((purTwistCompletedScalarMap Y l E).hom.app (op V) a))
        (purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V))
          ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
              (op V) b)
          (r.hom.app (op ((proEtaleBaseChange g).obj V))
              (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
                (purTwistZlOne Y l)).hom.app (op V) x))) := by
  intro V a b x
  have hroot : AlgebraicGeometry.Scheme.root_direct l g =
      ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
        (purTwistZlOne Y l)) ≫
        (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map r := by
    rw [hr]
    rfl
  have hs := root_completed_linear l g (op V) a x
  have hc := congrArg (fun k ↦ k.hom.app (op V) a) (completedScalar_square l E g)
  change (sfCompletedCoefficientMap l E g).hom.app (op V)
      ((purTwistCompletedScalarMap Y l E).hom.app (op V) a) =
    (purTwistCompletedScalarMap X l E).hom.app (op ((proEtaleBaseChange g).obj V))
      ((zlDirect l g).hom.app (op V) a) at hc
  rw [hroot] at hs
  change _ = @SMul.smul _ _
    (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul _ _
  rw [hc, (purTwistIntegralAction_existsUnique X l E).exists.choose_spec.2.2]
  exact congrArg (fun z ↦ purTwistIntegralTensor X l E
    (op ((proEtaleBaseChange g).obj V)) _ z) hs

end WeilConjectures
