/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition

/-! # Ordinary section-normalized finite direct-image compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.finite
  AlgebraicGeometry.Scheme.ProEt CategoryTheory.MorphismProperty
set_option backward.defeqAttrib.useBackward true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Transport an ordinary compositor through equal scalar maps.
Source: Stacks 03D1 and 03D6
(blueprint: lem-sf-finite-ring-ordinary-compositor-normalization). -/
def finiteScalarTransportCompositor {U V W : Scheme.{w}}
    (h : U ⟶ V) (k : V ⟶ W)
    (R : Sheaf (ProEt.topology U) CommRingCat.{w + 1})
    (S : Sheaf (ProEt.topology V) CommRingCat.{w + 1})
    (T : Sheaf (ProEt.topology W) CommRingCat.{w + 1})
    (a a' : S ⟶ (proEtaleSheafDirectImage h CommRingCat.{w + 1}).obj R)
    (b b' : T ⟶ (proEtaleSheafDirectImage k CommRingCat.{w + 1}).obj S)
    (c c' : T ⟶ (proEtaleSheafDirectImage (h ≫ k) CommRingCat.{w + 1}).obj R)
    (ha : a = a') (hb : b = b') (hc : c = c')
    (d : finiteScalarDirectImage h S R a' ⋙ finiteScalarDirectImage k T S b' ≅
      finiteScalarDirectImage (h ≫ k) T R c') :=
  Functor.isoWhiskerRight (eqToIso (congrArg (finiteScalarDirectImage h S R) ha))
          (finiteScalarDirectImage k T S b) ≪≫
        Functor.isoWhiskerLeft (finiteScalarDirectImage h S R a')
          (eqToIso (congrArg (finiteScalarDirectImage k T S) hb)) ≪≫ d ≪≫
        (eqToIso (congrArg (finiteScalarDirectImage (h ≫ k) T R) hc)).symm

private theorem scalar_transport_sections {U V W : Scheme.{w}}
    (h : U ⟶ V) (k : V ⟶ W)
    (R : Sheaf (ProEt.topology U) CommRingCat.{w + 1})
    (S : Sheaf (ProEt.topology V) CommRingCat.{w + 1})
    (T : Sheaf (ProEt.topology W) CommRingCat.{w + 1})
    (a a' : S ⟶ (proEtaleSheafDirectImage h CommRingCat.{w + 1}).obj R)
    (b b' : T ⟶ (proEtaleSheafDirectImage k CommRingCat.{w + 1}).obj S)
    (c c' : T ⟶ (proEtaleSheafDirectImage (h ≫ k) CommRingCat.{w + 1}).obj R)
    (ha : a = a') (hb : b = b') (hc : c = c')
    (d : finiteScalarDirectImage h S R a' ⋙ finiteScalarDirectImage k T S b' ≅
      finiteScalarDirectImage (h ≫ k) T R c')
    (M : proEtaleRingModules U R) (Z : W.ProEt)
    (x : M.val.obj (Opposite.op ((proEtaleBaseChange h).obj
      ((proEtaleBaseChange k).obj Z)))) :
    ((finiteScalarTransportCompositor h k R S T a a' b b' c c'
        ha hb hc d).hom.app M).val.app
          (Opposite.op Z) x =
      (d.hom.app M).val.app (Opposite.op Z) x := by
  unfold finiteScalarTransportCompositor
  cases ha
  cases hb
  cases hc
  simp only [eqToIso_refl, Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl, Iso.refl_symm]

private theorem scalar_transport_normalizes {U V W : Scheme.{w}}
    (h : U ⟶ V) (k : V ⟶ W)
    (R : Sheaf (ProEt.topology U) CommRingCat.{w + 1})
    (S : Sheaf (ProEt.topology V) CommRingCat.{w + 1})
    (T : Sheaf (ProEt.topology W) CommRingCat.{w + 1})
    (a a' : S ⟶ (proEtaleSheafDirectImage h CommRingCat.{w + 1}).obj R)
    (b b' : T ⟶ (proEtaleSheafDirectImage k CommRingCat.{w + 1}).obj S)
    (c c' : T ⟶ (proEtaleSheafDirectImage (h ≫ k) CommRingCat.{w + 1}).obj R)
    (ha : a = a') (hb : b = b') (hc : c = c')
    (d : finiteScalarDirectImage h S R a' ⋙ finiteScalarDirectImage k T S b' ≅
      finiteScalarDirectImage (h ≫ k) T R c')
    (hd : ∀ (M : proEtaleRingModules U R) (Z : W.ProEt)
      (x : M.val.obj (Opposite.op ((proEtaleBaseChange h).obj
        ((proEtaleBaseChange k).obj Z)))),
      (d.hom.app M).val.app (Opposite.op Z) x =
        M.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app Z).op x) :
    ∀ (M : proEtaleRingModules U R) (Z : W.ProEt)
      (x : M.val.obj (Opposite.op ((proEtaleBaseChange h).obj
        ((proEtaleBaseChange k).obj Z)))),
    ((finiteScalarTransportCompositor h k R S T a a' b b' c c'
        ha hb hc d).hom.app M).val.app
          (Opposite.op Z) x =
      M.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app Z).op x := by
  intro M Z x
  exact (scalar_transport_sections h k R S T a a' b b' c c' ha hb hc d M Z x).trans
    (hd M Z x)

/-- The intrinsic ordinary compositor, as the mate of pullback composition.
Source: Stacks 03D6 (blueprint: lem-sf-finite-ring-ordinary-compositor-normalization). -/
def finiteIntrinsicOrdinaryCompositor {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    proEtaleConstantModuleDirectImage h A ⋙ proEtaleConstantModuleDirectImage k A ≅
      proEtaleConstantModuleDirectImage (h ≫ k) A :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  conjugateIsoEquiv ((sfIntrinsicConstantModuleAdjunction k A).comp
    (sfIntrinsicConstantModuleAdjunction h A))
    (sfIntrinsicConstantModuleAdjunction (h ≫ k) A) (sfIntrinsicPullbackComp A h k)

/-- Transport the constant-section compositor along the finite scalar-map equalities.
Source: Stacks 03D1 and 03D6
(blueprint: lem-sf-finite-ring-ordinary-compositor-normalization). -/
def finiteTransportedOrdinaryCompositor {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) :=
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let A := Padic.coefficientExtensionRing l E (n + 1)
  finiteScalarTransportCompositor h k (R.ring U) (R.ring V) (R.ring W)
    (proEtaleRingDirectImageMap h (R.ring V) (R.ring U) (R.pull h))
    (proEtaleCoefficientDirectImageMap h A)
    (proEtaleRingDirectImageMap k (R.ring W) (R.ring V) (R.pull k))
    (proEtaleCoefficientDirectImageMap k A)
    (proEtaleRingDirectImageMap (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))
    (proEtaleCoefficientDirectImageMap (h ≫ k) A)
    (finiteRingDirectImageMap_eq l E n h) (finiteRingDirectImageMap_eq l E n k)
    (finiteRingDirectImageMap_eq l E n (h ≫ k))
    (finiteIntrinsicOrdinaryCompositor l E n h k)

attribute [local implicit_reducible] finiteScalarDirectImage
  proEtaleRingModuleDirectImage proEtaleConstantModuleDirectImage SheafOfModules.pushforward

/-- The transported ordinary compositor has the specified action on sections.
Source: Stacks 03D1 and 03D6
(blueprint: lem-sf-finite-ring-ordinary-compositor-normalization).

Proof: equality elimination in the three scalar-map equalities removes every
transport from the section map. The remaining intrinsic mate acts by restriction
along pullbackComp, by intrinsic_compositor_sections. This calculation uses no
coefficient composition hypothesis and no derived category. -/
theorem finiteTransportedOrdinaryCompositor_normalization
    {U V W : Scheme.{w}} (h : U ⟶ V) (k : V ⟶ W) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    ∀ (N : proEtaleRingModules U (R.ring U)) (T : W.ProEt)
      (m : N.val.obj (Opposite.op ((proEtaleBaseChange h).obj
        ((proEtaleBaseChange k).obj T)))) ,
      ((finiteTransportedOrdinaryCompositor l E n h k).hom.app N).val.app
          (Opposite.op T) m =
        N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app T).op m := by
  dsimp only [finiteTransportedOrdinaryCompositor]
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  refine scalar_transport_normalizes h k (R.ring U) (R.ring V) (R.ring W)
    (proEtaleRingDirectImageMap h (R.ring V) (R.ring U) (R.pull h))
    (proEtaleCoefficientDirectImageMap h (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleRingDirectImageMap k (R.ring W) (R.ring V) (R.pull k))
    (proEtaleCoefficientDirectImageMap k (Padic.coefficientExtensionRing l E (n + 1)))
    (proEtaleRingDirectImageMap (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))
    (proEtaleCoefficientDirectImageMap (h ≫ k) (Padic.coefficientExtensionRing l E (n + 1)))
    (finiteRingDirectImageMap_eq l E n h) (finiteRingDirectImageMap_eq l E n k)
    (finiteRingDirectImageMap_eq l E n (h ≫ k))
    (finiteIntrinsicOrdinaryCompositor l E n h k) ?_
  intro N T m
  dsimp only [finiteIntrinsicOrdinaryCompositor]
  rw [conjugateIsoEquiv_apply_hom]
  exact intrinsic_compositor_sections (Padic.coefficientExtensionRing l E (n + 1))
    h k N T m

end WeilConjectures.ConstructibleExceptionalCoefficients
