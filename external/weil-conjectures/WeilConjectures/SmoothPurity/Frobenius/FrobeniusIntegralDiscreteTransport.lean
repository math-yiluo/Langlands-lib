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
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusIntegralDiscreteTransportInvertible

/-! # Discrete tensor step of integral root transport

Source: Stacks Project, `sites-modules.tex`, Tags 03EK and 03EL.
(blueprint: new-weil-frobenius-integral-discrete-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] MorphismProperty.Over.pullback constantSheaf Padic
attribute [local instance_reducible] PurCompactSupport.completed

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

private theorem constantCompletion_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purTwistIntegralCompletionMap Y l E ≫ sfCompletedCoefficientMap l E g =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (purTwistIntegralCompletionMap X l E) := by
  apply completedDirect_hom_ext l E g
  intro n
  erw [Category.assoc, (sfCompletedCoefficientMap_existsUnique l E g).exists.choose_spec]
  erw [← Category.assoc,
    (purTwistIntegralCompletionMap_existsUnique Y l E).exists.choose_spec]
  erw [Category.assoc, ← Functor.map_comp,
    (purTwistIntegralCompletionMap_existsUnique X l E).exists.choose_spec]
  let q := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      ULift.ringEquiv.toRingHom))
  change (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map q ≫
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} _ =
    proEtaleConstantDirectImageMap g CommRingCat.{u + 1} _ ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map q)
  exact AlgebraicGeometry.Scheme.constant_naturality g q

/-- Discrete tensor extension of the prescribed root comparison.

Source: Stacks Project, `sites-modules.tex`, Sections "Sheaves of modules" and
"Tensor product", especially the tensor/restriction adjunction and
`lemma-tensor-product-pullback` (Tags 03EK and 03EL).
Proof: at level n the root comparison is linear over the constant Z/l^(n+1)
comparison. Projecting the inverse-limit map to every finite level therefore shows
linearity over the constant Z_l sheaf. The bilinear map (b,x) to b' tensor r(x')
is balanced over this constant sheaf. Its tensor lift commutes with restriction,
and its sheafification is the asserted map. Along a scheme isomorphism, direct
image is transport by an equivalence of sites. The constant scalar comparison and
the root comparison are invertible, so the inverse balanced map sheafifies to its
inverse. The two composites are identities on pure tensors and hence everywhere
by local tensor generation. Finally the completed action of a constant integral
scalar is its ordinary discrete action; naturality of the constant-to-completed
map follows after every finite coefficient projection. This gives the last formula.
No root trivialization or invertibility of l on the schemes is required.
(blueprint: new-weil-frobenius-integral-discrete-transport). -/
theorem frobeniusIntegralDiscreteTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (r : (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).obj
      (purTwistZlOne Y l) ⟶ purTwistZlOne X l)
    (hr : r = limit.post (proEtaleRootsOfUnityTower Y l Fact.out)
        (proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}) ≫
      lim.map (((proEtaleRootsOfUnityInverseImageIso g).2.1 l Fact.out).choose))
    (hrIso : IsIso r) :
    ∃ φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)),
      IsIso φ ∧
      (∀ (V : Y.ProEt) (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
        (x : (purTwistZlOne Y l).obj.obj (op V)),
        φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) b x) =
          purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V))
            ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
              (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom.app
              (op V) b)
            (r.hom.app (op ((proEtaleBaseChange g).obj V))
              (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
                (purTwistZlOne Y l)).hom.app (op V) x))) ∧
      (∀ (V : Y.ProEt) (b : (purTwistIntegralConstant Y l E).obj.obj (op V))
        (t : (purTwistIntegralOne Y l E).val.obj (op V)),
        φ.hom.app (op V) (b • t) =
          @SMul.smul _ _
            (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul
            ((sfCompletedCoefficientMap l E g).hom.app (op V)
              ((purTwistIntegralCompletionMap Y l E).hom.app (op V) b))
            (φ.hom.app (op V) t)) := by
  let M (T : Scheme.{u}) :=
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)
  let b := proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))
  let f := AlgebraicGeometry.Scheme.tensor_direct
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange g)
    (purTwistConstantIntegersMap Y l E) (purTwistConstantIntegersMap X l E)
    (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) b
    (AlgebraicGeometry.Scheme.constant_naturality g _)
    (M Y) (M X) (AlgebraicGeometry.Scheme.root_direct l g)
    (fun U a x ↦ AlgebraicGeometry.Scheme.root_limit_linear l g U.unop a x)
  let φ : (SheafOfModules.toSheaf _).obj (purTwistIntegralModule Y l E) ⟶
      (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf _).obj (purTwistIntegralModule X l E)) :=
    (SheafOfModules.toSheaf _).map f
  have hroot : AlgebraicGeometry.Scheme.root_direct l g =
      ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
        (purTwistZlOne Y l)) ≫
        (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map r := by
    rw [hr]
    rfl
  have hform (V : Y.ProEt) (s : (purTwistIntegralConstant Y l E).obj.obj (op V))
      (x : (purTwistZlOne Y l).obj.obj (op V)) :
      φ.hom.app (op V) (purTwistIntegralTensor Y l E (op V) s x) =
        purTwistIntegralTensor X l E (op ((proEtaleBaseChange g).obj V))
          (b.hom.app (op V) s)
          (r.hom.app (op ((proEtaleBaseChange g).obj V))
            (((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).unit.app
              (purTwistZlOne Y l)).hom.app (op V) x)) := by
    have ht := AlgebraicGeometry.Scheme.tensor_direct_pure
      (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange g)
      (purTwistConstantIntegersMap Y l E) (purTwistConstantIntegersMap X l E)
      (proEtaleConstantDirectImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) b
      (AlgebraicGeometry.Scheme.constant_naturality g _)
      (M Y) (M X) (AlgebraicGeometry.Scheme.root_direct l g)
      (fun U a y ↦ AlgebraicGeometry.Scheme.root_limit_linear l g U.unop a y)
      (op V) s x
    refine ht.trans ?_
    rw [hroot]
    rfl
  refine ⟨φ, frobeniusIntegralDiscreteTransport_isIso l E g r hr hrIso φ hform,
    hform, ?_⟩
  intro V s t
  have hc := congrArg (fun k ↦ k.hom.app (op V) s) (constantCompletion_square l E g)
  change (sfCompletedCoefficientMap l E g).hom.app (op V)
      ((purTwistIntegralCompletionMap Y l E).hom.app (op V) s) =
    (purTwistIntegralCompletionMap X l E).hom.app
      (op ((proEtaleBaseChange g).obj V)) (b.hom.app (op V) s) at hc
  have ht := (f.val.app (op V)).hom.map_smul s t
  exact ht.trans (by
    change _ = @SMul.smul _ _
      (purTwistIntegralAction X l E (op ((proEtaleBaseChange g).obj V))).toSMul _ _
    rw [hc, (purTwistIntegralAction_existsUnique X l E).exists.choose_spec.2.1]
    rfl)

end WeilConjectures
