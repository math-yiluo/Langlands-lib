/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # The actual finite constant-coefficient ring adjunct

Source: Stacks Tags 04B3, 0H7J, 09A5 and 03CY.
(blueprint: lem-fix-qcqs-ordinary-finite-coefficient-isos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice

private noncomputable instance ringSheafify (Z : Scheme.{t}) :
    HasSheafify (ProEt.topology Z) RingCat.{max u (t + 1)} :=
  let : EssentiallySmall.{max u (t + 1)} Z.ProEt := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

private instance ringWeakSheafify (Z : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology Z) RingCat.{max u (t + 1)} :=
  (ringSheafify.{t, u} Z).isRightAdjoint

private instance commRingWeakSheafify (Z : Scheme.{t}) :
    HasWeakSheafify (ProEt.topology Z) CommRingCat.{max u (t + 1)} :=
  (integralCoefficientRingSheafify.{t, u} Z).isRightAdjoint

private noncomputable instance forgetCommRingSheafification (Z : Scheme.{t}) :
    (ProEt.topology Z).PreservesSheafification
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) := by
  let e := AsSmall.equiv.{t, t + 1, max u (t + 1)} (C := Z.ProEt)
  let K := e.inverse.inducedTopology (ProEt.topology Z)
  let H := forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}
  let : K.PreservesSheafification H :=
    GrothendieckTopology.instPreservesSheafification K H
      (FD := fun A B : CommRingCat.{max u (t + 1)} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u (t + 1)} ↦ A)
      (FE := fun A B : RingCat.{max u (t + 1)} ↦ A →+* B)
      (CE := fun A : RingCat.{max u (t + 1)} ↦ A)
  exact GrothendieckTopology.PreservesSheafification.transport
    (A := CommRingCat.{max u (t + 1)}) (ProEt.topology Z) K e.inverse
    RingCat.{max u (t + 1)} H

private theorem constant_forget_unit (Z : Scheme.{t})
    (A : CommRingCat.{max u (t + 1)}) :
    Functor.whiskerRight
        (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}) ≫
      ((constantCommuteCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).hom.app A).hom =
    toSheafify (ProEt.topology Z)
      ((Functor.const Z.ProEtᵒᵖ).obj
        ((forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}).obj A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac]
  rw [← toSheafify_naturality]
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

private theorem ring_constant_map_isIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : RingCat.{max u (t + 1)}) :
    IsIso (((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} f)).homEquiv _ _).symm
      (((sheafificationAdjunction (ProEt.topology Y) RingCat.{max u (t + 1)}).homEquiv
        _ _).symm
        (Functor.whiskerLeft (proEtaleBaseChange f).op
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A))))) := by
  let T := ⊤_ Y.ProEt
  let hT := terminalIsTerminal (C := Y.ProEt)
  let hGT := hT.isTerminalObj (proEtaleBaseChange f)
  let a := Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} f)
  let aY := constantSheafAdj (ProEt.topology Y) RingCat.{max u (t + 1)} hT
  let aX := constantSheafAdj (ProEt.topology X) RingCat.{max u (t + 1)} hGT
  let b := (aY.comp a).ofNatIsoRight
    ((proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      RingCat.{max u (t + 1)} (ProEt.topology Y) (ProEt.topology X) (op T))
  let ρ : (constantSheaf (ProEt.topology Y) RingCat.{max u (t + 1)}).obj A ⟶
      (ordinaryRingPush.{t, u} f).obj
        ((constantSheaf (ProEt.topology X) RingCat.{max u (t + 1)}).obj A) :=
    ((sheafificationAdjunction (ProEt.topology Y)
      RingCat.{max u (t + 1)}).homEquiv _ _).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  have he : (a.homEquiv _ _).symm ρ = (b.leftAdjointUniq aX).hom.app A := by
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_ofNatIsoRight_apply]
    change (aY.comp a).homEquiv _ _ ((a.homEquiv _ _).symm ρ) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change aY.homEquiv _ _ (a.homEquiv _ _ ((a.homEquiv _ _).symm ρ)) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj RingCat.{max u (t + 1)} hT).comp
      (sheafificationAdjunction (ProEt.topology Y)
        RingCat.{max u (t + 1)})).homEquiv _ _ ρ = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj RingCat.{max u (t + 1)} hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y)
        RingCat.{max u (t + 1)}).homEquiv _ _
          (((sheafificationAdjunction (ProEt.topology Y)
            RingCat.{max u (t + 1)}).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  change IsIso ((a.homEquiv _ _).symm ρ)
  rw [he]
  infer_instance

private noncomputable abbrev forgottenConstantDirectRingMap
    {X Y : Scheme.{t}} (f : X ⟶ Y) (A : CommRingCat.{max u (t + 1)}) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ⟶
      (ordinaryRingPush.{t, u} f).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A)) :=
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (coefficientProEtaleDirectRingMap f A)

-- Keep the ring abstract while checking the sheafification and adjunction equations.
private theorem constant_ring_adjunct_isIso
    {X Y : Scheme.{t}} (f : X ⟶ Y) (A : CommRingCat.{max u (t + 1)}) :
    IsIso (((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} f)).homEquiv _ _).symm
      (forgottenConstantDirectRingMap f A)) := by
  let H := forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}
  let eY : (sheafCompose (ProEt.topology Y) H).obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) ≅
      (constantSheaf (ProEt.topology Y) RingCat.{max u (t + 1)}).obj (H.obj A) :=
    (constantCommuteCompose (ProEt.topology Y) H).app A
  let eX : (sheafCompose (ProEt.topology X) H).obj
      ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A) ≅
      (constantSheaf (ProEt.topology X) RingCat.{max u (t + 1)}).obj (H.obj A) :=
    (constantCommuteCompose (ProEt.topology X) H).app A
  let G := ordinaryRingPush.{t, u} f
  let a := Adjunction.ofIsRightAdjoint G
  let ρ : (constantSheaf (ProEt.topology Y) RingCat.{max u (t + 1)}).obj (H.obj A) ⟶
      G.obj ((constantSheaf (ProEt.topology X) RingCat.{max u (t + 1)}).obj (H.obj A)) :=
    ((sheafificationAdjunction (ProEt.topology Y)
      RingCat.{max u (t + 1)}).homEquiv _ _).symm
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (H.obj A))))
  have hρ : toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (H.obj A)) ≫ ρ.hom =
      Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (H.obj A))) :=
    ((sheafificationAdjunction (ProEt.topology Y)
      RingCat.{max u (t + 1)}).homEquiv _ _).apply_symm_apply _
  have hη (Z : Scheme.{t}) : toSheafify (ProEt.topology Z)
      ((Functor.const Z.ProEtᵒᵖ).obj (H.obj A)) ≫
        ((constantCommuteCompose (ProEt.topology Z) H).inv.app A).hom =
      Functor.whiskerRight
        (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A)) H := by
    let e := (constantCommuteCompose (ProEt.topology Z) H).app A
    calc
      _ = (Functor.whiskerRight
          (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A)) H ≫
            e.hom.hom) ≫ e.inv.hom :=
        congrArg (fun q ↦ q ≫ e.inv.hom) (constant_forget_unit Z A).symm
      _ = Functor.whiskerRight
          (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A)) H ≫
            (e.hom ≫ e.inv).hom := by
        simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      _ = _ := by rw [e.hom_inv_id]; exact Category.comp_id _
  have hYη : toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (H.obj A)) ≫ eY.inv.hom =
      Functor.whiskerRight
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) H := hη Y
  have hXη : Functor.whiskerRight
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)) H ≫ eX.hom.hom =
      toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (H.obj A)) :=
    constant_forget_unit X A
  have hc : forgottenConstantDirectRingMap f A ≫ G.map eX.hom = eY.hom ≫ ρ := by
    apply (cancel_epi eY.inv).1
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (G.obj ((constantSheaf _ _).obj (H.obj A))).property
    change toSheafify _ _ ≫ (eY.inv.hom ≫
        ((forgottenConstantDirectRingMap f A).hom ≫ (G.map eX.hom).hom)) =
      toSheafify _ _ ≫ (eY.inv.hom ≫ (eY.hom ≫ ρ).hom)
    rw [← Category.assoc, hYη]
    have hunit : toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A) ≫
        (coefficientProEtaleDirectRingMap f A).hom =
        Functor.whiskerLeft (proEtaleBaseChange f).op
          (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)) :=
      ((sheafificationAdjunction (ProEt.topology Y)
        CommRingCat.{max u (t + 1)}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X)
              CommRingCat.{max u (t + 1)}).obj A))).apply_symm_apply _
    have hC := congrArg (fun q ↦ Functor.whiskerRight q H) hunit
    change Functor.whiskerRight (toSheafify _ _) H ≫
        ((Functor.whiskerRight (coefficientProEtaleDirectRingMap f A).hom H) ≫
          Functor.whiskerLeft (proEtaleBaseChange f).op eX.hom.hom) = _
    rw [← Category.assoc, ← Functor.whiskerRight_comp, hC]
    change Functor.whiskerLeft (proEtaleBaseChange f).op
        (Functor.whiskerRight (toSheafify _ _) H ≫ eX.hom.hom) = _
    rw [hXη]
    change _ = toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj (H.obj A)) ≫
      (eY.inv ≫ eY.hom ≫ ρ).hom
    rw [Iso.inv_hom_id_assoc]
    exact hρ.symm
  have he : (a.homEquiv _ _).symm (forgottenConstantDirectRingMap f A) ≫ eX.hom =
      (ordinaryRingInverse.{t, u} f).map eY.hom ≫ (a.homEquiv _ _).symm ρ := by
    rw [← a.homEquiv_naturality_right_symm, hc, a.homEquiv_naturality_left_symm]
  have : IsIso ((a.homEquiv _ _).symm ρ) := ring_constant_map_isIso f (H.obj A)
  have : IsIso ((a.homEquiv _ _).symm (forgottenConstantDirectRingMap f A) ≫ eX.hom) := by
    rw [he]
    exact inferInstanceAs (IsIso (((ordinaryRingInverse.{t, u} f).mapIso eY ≪≫
      asIso ((a.homEquiv _ _).symm ρ)).hom))
  exact IsIso.of_isIso_comp_right _ eX.hom

/-- The actual finite coefficient constant-section map has invertible ring adjunct,
with independent scheme and coefficient universes, for every scheme morphism.

Source: Stacks Tags 04B3, 0H7J, 09A5 and 03CY.
(blueprint: lem-fix-qcqs-ordinary-finite-coefficient-isos)

Proof: constant sheafification is left adjoint to evaluation at a terminal site
object. Base change preserves that terminal object. Composing its ring inverse-image
adjunction with the constant-sheaf adjunction gives another left adjoint to the same
evaluation functor. Uniqueness of left adjoints identifies the adjunct of the
constant-section direct map with an isomorphism. Forgetting commutativity commutes
with sheafification: the comparison respects the sheafification unit. Its unit
equation identifies the prescribed forgotten commutative-ring map with the ring
constant-section map, conjugated by the two constant-sheaf comparison isomorphisms.
Transpose this square through the ring adjunction and cancel those isomorphisms.
The argument is made for an arbitrary commutative ring before specializing to the
lifted quotient ring; it needs no nonemptiness assumption and includes the zero ring. -/
theorem ordinaryFiniteCoefficientMap_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (((Adjunction.ofIsRightAdjoint (ordinaryRingPush.{t, u} f)).homEquiv _ _).symm
      (ordinaryFiniteRingMap l E f n)) := by
  exact constant_ring_adjunct_isIso f
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

end WeilConjectures.IntegralOnSlice
