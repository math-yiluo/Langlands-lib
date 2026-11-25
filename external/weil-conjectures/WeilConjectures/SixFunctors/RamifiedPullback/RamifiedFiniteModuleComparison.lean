/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedPullbackTowerData
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedCoefficientModuleBaseChange
import WeilConjectures.SixFunctors.RamifiedPullback.RamifiedFiniteScalarComposition

/-! # Ramified comparison for individual module sheaves

Source: Stacks Project, Tags 03EK and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The module functor whose termwise extension is the finite pullback level.
Source: Stacks 03EL (blueprint: lem-weil-ramified-finite-module-comparison). -/
abbrev finitePullbackModule {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ) :=
  unrestrictedIntegralReductionFunctor l E Y n ⋙
    integralOperationsLevelPullback l E g n ⋙
      SheafOfModules.restrictScalars
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
            (completedIntegralCommRingProjectionUnrestricted l E X n))

/-- The two finite coefficients in a module pullback generator.
Source: Stacks 03EL (blueprint: lem-weil-ramified-finite-module-comparison). -/
abbrev finitePullbackModuleTensor {X Y : Scheme.{t}} (g : X ⟶ Y) (n : ℕ)
    (M : integralTowerModules l E Y) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
    (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange g).obj V))) (p : M.val.obj (op V)) :
    ((finitePullbackModule l E g n).obj M).val.obj
      (op ((Scheme.proEtaleBaseChange g).obj V)) :=
  b • @id (((integralOperationsLevelPullback l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj M)).val.obj
        (op ((Scheme.proEtaleBaseChange g).obj V)))
    (integralOperationsPullbackGenerator l E g n _ V
      (unrestrictedIntegralTensorSection l E Y n M (op V) a p))

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Objectwise normalized comparison at one finite level, before naturality,
complexes, or transition maps.
Source: Stacks 03EL (lemma-tensor-product-pullback) and 03EK (section-tensor-product).
(blueprint: lem-weil-ramified-finite-module-comparison).

Proof: Write R and S for the completed E and L coefficient sheaves. Express the
finite E pullback as g-inverse(M) tensor over g-inverse(R_Y) with the finite E
coefficient sheaf on X. This identification follows by pulling back the finite
reduction tensor and cancelling the intermediate finite coefficient ring on Y;
the forward map multiplies the pulled-back finite coefficient into the X factor,
and the inverse inserts one. Extend scalars to S_X and reassociate. The given
coefficientIso on X identifies the last two factors with the finite L quotient.
On the other side, pull back M tensor over R_Y with S_Y, and tensor with the
finite L quotient on X. The intermediate g-inverse(S_Y) cancels by multiplication,
with inverse insertion of one. Composing the first identification with the inverse
of the second gives the displayed isomorphism for each M. All maps are balanced
and linear over S_X. The coefficient_formula gives its last factor; naturality of
constant-ring structure maps with respect to j gives its first finite factor.
Thus evaluation on the nested tensor generator gives exactly the formula below.
The two composites are identities on tensors and hence after sheafification.
No naturality in M, cochain differential, or tower compatibility is asserted here.
The argument uses ordinary balanced tensors, so applies to zero modules and empty
sites and requires neither flatness nor a positive ramification index. -/
theorem finiteModuleComparison_exists {X Y : Scheme.{t}} (g : X ⟶ Y)
    (e : ℕ)
    (j : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1))
    (source : Coefficients l E L ι e j Y) (target : Coefficients l E L ι e j X)
    (n : ℕ) :
    ∃ d : ∀ M : integralTowerModules l E Y,
      (scalar.{t, u} target.completedMap).obj ((finitePullbackModule l E g n).obj M) ≅
        (finitePullbackModule l L g (index e n)).obj ((scalar.{t, u} source.completedMap).obj M),
      ∀ (M : integralTowerModules l E Y) (V : Y.ProEt)
        (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj (op V))
        (b : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange g).obj V)))
        (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj
          (op ((Scheme.proEtaleBaseChange g).obj V))) (p : M.val.obj (op V)),
      (d M).hom.val.app _
        (tensor.{t, u} target.completedMap ((finitePullbackModule l E g n).obj M)
          _ s (finitePullbackModuleTensor l E g n M V a b p)) =
        finitePullbackModuleTensor l L g (index e n) ((scalar.{t, u} source.completedMap).obj M) V
          ((ramifiedMap l E L Y e n (j n)).hom.app (op V) a)
          ((ramifiedMap l E L X e n (j n)).hom.app _ b *
            (completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s)
          (tensor.{t, u} source.completedMap M (op V) 1 p) := by
  obtain ⟨b, hb⟩ := coefficientModuleBaseChange_exists l E L ι X e j target n
  obtain ⟨d, hd⟩ := finiteScalarComposition_exists l E L ι g e j source n
  let R := SheafOfModules.restrictScalars
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l L X (index e n)))
  let D (M : integralTowerModules l E Y) :=
    b ((integralOperationsLevelPullback l E g n).obj
        ((unrestrictedIntegralReductionFunctor l E Y n).obj M)) ≪≫ R.mapIso (d M)
  refine ⟨D, ?_⟩
  intro M V a b' s p
  change (d M).hom.val.app _
    ((b ((integralOperationsLevelPullback l E g n).obj
      ((unrestrictedIntegralReductionFunctor l E Y n).obj M))).hom.val.app _
        (tensor.{t, u} target.completedMap _ _ s
          (finitePullbackModuleTensor l E g n M V a b' p))) = _
  rw [hb]
  simpa only [finitePullbackModuleTensor, mul_comm, id_eq] using
    hd M V a b'
      ((completedIntegralCommRingProjectionUnrestricted l L X (index e n)).hom.app _ s) p

end WeilConjectures.RamifiedPullback
