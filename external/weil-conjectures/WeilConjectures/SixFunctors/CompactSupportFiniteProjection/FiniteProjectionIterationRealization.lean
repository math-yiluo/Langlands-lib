/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.UnitTensorRealization

/-! # Realizing an iteration of two finite projection maps

The comparisons here are explicit composites of the coefficient units and the
published support and pullback realizations. No compact-support compositor occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorFiniteOperations D C E n hn)
  {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
  (K : sixFunctorFiniteCategory D C E n hn X)
  (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)

/-- Realization of the tensor of an iterated support value. It first realizes the
outer support, then tensors the inner support comparison.
Source: coefficient transport in fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-projection-iteration-realization). -/
def iterationSourceComparison :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let TZ := fixedTensor (C := C) (E := E) (n := n) Z
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
  sourceComparison S g cg ((S.finite.support f cf).obj K) L ≪≫
    RZ.functor.mapIso ((TZ.mapIso (G.mapIso (fixedSupportRealization S f cf K))).app
      (RZ.inverse.obj L.obj))

/-- Cancel the tensor coefficient unit, and realize the two successive pullbacks.
Source: coefficient transport in fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-projection-iteration-realization). -/
def iterationTensorComparison :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let Pf := fixedDerivedPull (C := C) (E := E) (n := n) f
  unitTensorRealization RX TX (RX.inverse.obj K.obj)
    (fixedPullRealization S f
        ⟨((torPull S g).obj L).obj, ((torPull S g).obj L).property.1⟩ ≪≫
        Pf.mapIso (fixedPullRealization S g ⟨L.obj, L.property.1⟩))

/-- Realize the two supports and cancel the coefficient unit at their tensor input.
Source: coefficient transport in fix-prop-projection-formula.proof.md
(blueprint: lem-sf-finite-projection-iteration-realization). -/
def iterationTargetComparison :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
  let M := ((partialTensor S X).obj K).obj ((torPull S f).obj ((torPull S g).obj L))
  supportRealization S g cg ((S.finite.support f cf).obj M) ≪≫
    RZ.functor.mapIso (G.mapIso (fixedSupportRealization S f cf M)) ≪≫
    RZ.functor.mapIso (G.mapIso (F.mapIso (iterationTensorComparison S f g K L)))

private theorem map_two_eq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b c d : A} {p : a ⟶ b} {q : b ⟶ d} {r : a ⟶ c} {s : c ⟶ d}
    (h : p ≫ q = r ≫ s) : F.map p ≫ F.map q = F.map r ≫ F.map s := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem map_three_eq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b c d e f : A} {p : a ⟶ b} {q : b ⟶ c} {r : c ⟶ f}
    {s : a ⟶ d} {t : d ⟶ e} {u : e ⟶ f}
    (h : p ≫ q ≫ r = s ≫ t ≫ u) :
    F.map p ≫ F.map q ≫ F.map r = F.map s ≫ F.map t ≫ F.map u := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem split_map_tail
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b : B} {x y z : A} {p : a ⟶ b} {q : b ⟶ F.obj x}
    {u : x ⟶ y} {v : y ⟶ z} {r : a ⟶ F.obj z}
    (h : p ≫ q ≫ F.map (u ≫ v) = r) :
    p ≫ q ≫ F.map u ≫ F.map v = r := by
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem combine_map_path
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {a b c : A} {d e f : B} (p : a ⟶ b) (q : b ⟶ c)
    (x : F.obj c ⟶ d) (y : d ⟶ e) (z : e ⟶ f) {r : F.obj a ⟶ f}
    (h : F.map p ≫ F.map q ≫ x ≫ y ≫ z = r) :
    F.map (p ≫ q) ≫ x ≫ y ≫ z = r := by
  simpa only [Functor.map_comp, Category.assoc] using h

private theorem diagram_transport
    {A : Type*} [Category A]
    {a b c d e f a₁ a₂ a₃ b₃ c₁ c₂ c₃ d₂ f₁ : A}
    {p : a ⟶ b} {q : b ⟶ c} {x : c ⟶ d} {y : d ⟶ e} {z : e ⟶ f}
    {u : a ⟶ a₁} {v : a₁ ⟶ a₂} {w : a₂ ⟶ a₃} {r : a₃ ⟶ b₃} {s : b₃ ⟶ f}
    {p' : a₂ ⟶ d₂} {x' : b ⟶ c₁} {q' : c₁ ⟶ d}
    {z₁ : e ⟶ f₁} {z₂ : f₁ ⟶ f}
    {u' : c₁ ⟶ c₂} {t : c₂ ⟶ c₃} {r' : c₃ ⟶ f₁}
    {v' : c₂ ⟶ d₂} {w' : d₂ ⟶ b₃} {s' : c₃ ⟶ b₃}
    (hs : q ≫ x = x' ≫ q')
    (hf : q' ≫ y ≫ z₁ = u' ≫ t ≫ r')
    (hg : p ≫ x' ≫ u' ≫ v' = u ≫ v ≫ p')
    (hnf : s' ≫ s = r' ≫ z₂) (hty : v' ≫ w' = t ≫ s')
    (hng : w ≫ r = p' ≫ w') (hz : z = z₁ ≫ z₂) :
    p ≫ q ≫ x ≫ y ≫ z = u ≫ v ≫ w ≫ r ≫ s := by
  rw [hz]
  rw [reassoc_of% hs, reassoc_of% hf, ← hnf,
    ← reassoc_of% hty, reassoc_of% hg, ← reassoc_of% hng]

private theorem map_iso_tensor_trans
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H : A ⥤ B) (T : C ⥤ A) {a : A} {x y z : C}
    (u : a ≅ T.obj x) (v : x ≅ y) (w : y ≅ z) :
    H.map (u ≪≫ T.mapIso (v ≪≫ w)).hom =
      H.map (u ≪≫ T.mapIso v).hom ≫ H.map (T.map w.hom) := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

private theorem map_unit_tensor_trans
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : A ≌ B) (H : A ⥤ C) (T : A ⥤ A ⥤ A) (k : A)
    {b : B} {c d : A} (e : R.inverse.obj b ≅ c) (h : c ≅ d) :
    H.map (unitTensorRealization R T k (e ≪≫ h)).hom =
      H.map (unitTensorRealization R T k e).hom ≫ H.map ((T.obj k).map h.hom) := by
  unfold unitTensorRealization
  exact map_iso_tensor_trans H (T.obj k) (R.unitIso.app _).symm e h

private theorem inverse_conjugation
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x y : B} {a b : A} (e : x ≅ R.functor.obj a) (d : y ≅ R.functor.obj b)
    (p : a ⟶ b) :
    R.inverse.map (e.hom ≫ R.functor.map p ≫ d.inv) ≫
        R.inverse.map d.hom ≫ R.unitIso.inv.app b =
      R.inverse.map e.hom ≫ R.unitIso.inv.app a ≫ p := by
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  rw [← R.inverse.map_comp_assoc d.inv d.hom, d.inv_hom_id, R.inverse.map_id,
    Category.id_comp]
  rw [← Functor.comp_map, R.unitIso.inv.naturality]
  rfl

private theorem inverse_unit_naturality
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {a b : A} (p : a ⟶ b) :
    R.inverse.map (R.functor.map p) ≫ R.unitIso.inv.app b =
      R.unitIso.inv.app a ≫ p := R.unitIso.inv.naturality p

private theorem inverse_conjugation_factored
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {x a b c : A} {y : B} (e : x ≅ a) (s : y ≅ R.functor.obj b)
    (d : b ≅ c) (p : a ⟶ c) :
    R.inverse.map
        ((R.functor.mapIso e).hom ≫ R.functor.map p ≫
          (s ≪≫ R.functor.mapIso d).inv) ≫
        (R.inverse.mapIso s ≪≫ (R.unitIso.app b).symm).hom ≫ d.hom =
      R.unitIso.inv.app x ≫ e.hom ≫ p := by
  have h := inverse_conjugation R (R.functor.mapIso e) (s ≪≫ R.functor.mapIso d) p
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] at h
  rw [inverse_unit_naturality R d.hom,
    reassoc_of% inverse_unit_naturality R e.hom] at h
  simpa -implicitDefEqProofs only [Functor.map_comp, Functor.mapIso_hom, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Category.assoc] using h

private theorem realize_of_inverse
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {u a b c : A} {y : B} (p : R.functor.obj u ⟶ y)
    (e : u ≅ a) (s : y ≅ R.functor.obj b) (d : b ≅ c) (q : a ⟶ c)
    (h : R.inverse.map p ≫
      (R.inverse.mapIso s ≪≫ (R.unitIso.app b).symm).hom ≫ d.hom =
        R.unitIso.inv.app u ≫ e.hom ≫ q) :
    p ≫ (s ≪≫ R.functor.mapIso d).hom =
      (R.functor.mapIso e).hom ≫ R.functor.map q := by
  apply R.inverse.map_injective
  apply (cancel_mono (R.unitIso.inv.app c)).1
  simp -implicitDefEqProofs only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [inverse_unit_naturality R d.hom, inverse_unit_naturality R q,
    reassoc_of% inverse_unit_naturality R e.hom]
  simpa -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc] using h

private theorem realize_of_inverse_two
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    {u v a b w c : A} {y : B} (p : R.functor.obj u ⟶ y)
    (e₁ : u ≅ v) (e₂ : v ≅ a) (s : y ≅ R.functor.obj b)
    (d₁ : b ≅ w) (d₂ : w ≅ c) (q : a ⟶ c)
    (h : R.inverse.map p ≫
      (R.inverse.mapIso s ≪≫ (R.unitIso.app b).symm).hom ≫ d₁.hom ≫ d₂.hom =
        R.unitIso.inv.app u ≫ e₁.hom ≫ e₂.hom ≫ q) :
    p ≫ (s ≪≫ R.functor.mapIso d₁ ≪≫ R.functor.mapIso d₂).hom =
      (R.functor.mapIso e₁ ≪≫ R.functor.mapIso e₂).hom ≫ R.functor.map q := by
  have h' := realize_of_inverse R p (e₁ ≪≫ e₂) s (d₁ ≪≫ d₂) q (by
    simpa -implicitDefEqProofs only [Iso.trans_hom, Category.assoc] using h)
  simpa -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, R.functor.map_comp,
    Category.assoc] using h'

private theorem fixed_support_naturality
    {K K' : sixFunctorFiniteCategory D C E n hn X} (a : K ⟶ K') :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
    let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
    RY.inverse.map (IY.map ((S.finite.support f cf).map a)) ≫
        (fixedSupportRealization S f cf K').hom =
      (fixedSupportRealization S f cf K).hom ≫ F.map (RX.inverse.map (IX.map a)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let IX := (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι
  let F := sixFunctorFiniteSupport D C E n hn f cf
  let H := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
  let e := S.finiteSupport f cf ≪≫ Functor.isoWhiskerLeft IX
    (Functor.isoWhiskerRight RX.counitIso.symm F ≪≫
      Functor.isoWhiskerLeft RX.inverse
        (sfIntrinsicCompactSupportComparison (Padic.coefficientExtensionRing C.l E n) cf))
  let d := Functor.isoWhiskerRight e RY.inverse ≪≫
    Functor.isoWhiskerLeft (IX ⋙ RX.inverse ⋙ H) RY.unitIso.symm
  exact d.hom.naturality a

private theorem fixed_projection_first
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K K' : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : K ⟶ K')
    (N : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a)).app N ≫
        projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c K' N =
      projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c K N ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map a).app
            (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).obj N)) := by
  exact congr_app ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).naturality a) N

private theorem fixed_projection_second
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)))
    {N N' : DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (a : N ⟶ N') :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)).map a ≫
        projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c K N' =
      projectionTensorCoordinateComponent (ModuleCat.{u + 1} A) c K N ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).map
            (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).map a)) := by
  exact ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).naturality a

private theorem fixed_component_realization
    (N : finiteTorConstructibleCategory C.l E n hn Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
    let IY := (intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
    let TX := fixedTensor (C := C) (E := E) (n := n) X
    let TY := fixedTensor (C := C) (E := E) (n := n) Y
    let k := RX.inverse.obj K.obj
    let l := RY.inverse.obj N.obj
    let M := ((partialTensor S X).obj K).obj ((torPull S f).obj N)
    RY.inverse.map (IY.map (component S f cf K N)) ≫
        (fixedSupportRealization S f cf M).hom ≫
        F.map ((RX.unitIso.app
          ((TX.obj k).obj (RX.inverse.obj ((torPull S f).obj N).obj))).inv ≫
          (TX.obj k).map (fixedPullRealization S f ⟨N.obj, N.property.1⟩).hom) =
      (RY.unitIso.app ((TY.obj (RY.inverse.obj ((S.finite.support f cf).obj K).obj)).obj
        l)).inv ≫ ((TY.map (fixedSupportRealization S f cf K).hom).app l) ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k l := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
  let M := ((partialTensor S X).obj K).obj ((torPull S f).obj N)
  let d := (RX.unitIso.app
    ((TX.obj (RX.inverse.obj K.obj)).obj (RX.inverse.obj ((torPull S f).obj N).obj))).symm ≪≫
      (TX.obj (RX.inverse.obj K.obj)).mapIso
        (fixedPullRealization S f ⟨N.obj, N.property.1⟩)
  have h := inverse_conjugation_factored RY
    ((TY.mapIso (fixedSupportRealization S f cf K)).app (RY.inverse.obj N.obj))
    (supportRealization S f cf M) (F.mapIso d)
    (fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf
      (RX.inverse.obj K.obj) (RY.inverse.obj N.obj))
  change RY.inverse.map
    ((intrinsicFiniteTorsionConstructible C.l E n hn Y.obj.left).ι.map
      (component S f cf K N)) ≫ _ = _ at h
  exact h

private theorem fixed_projection_first_coordinates
    {k k' : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))}
    (a : k ⟶ k')
    (N : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
    ((fixedTensor (C := C) (E := E) (n := n) Y).map (F.map a)).app N ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k' N =
      fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k N ≫ F.map
        (((fixedTensor (C := C) (E := E) (n := n) X).map a).app
          ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj N)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact fixed_projection_first (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) cf a N

private theorem fixed_projection_second_coordinates
    (k : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    {N N' : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))}
    (a : N ⟶ N') :
    let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
    ((fixedTensor (C := C) (E := E) (n := n) Y).obj (F.obj k)).map a ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k N' =
      fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k N ≫ F.map
        (((fixedTensor (C := C) (E := E) (n := n) X).obj k).map
          ((fixedDerivedPull (C := C) (E := E) (n := n) f).map a)) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact fixed_projection_second (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)) cf k a

-- Match the coordinate APIs without opening coefficient equivalences or tensor resolutions.
attribute [local irreducible] realization fixedTensor fixedDerivedPull component fixedComponent
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor

/-- Iterating two conjugated projection components realizes the iteration of the
fixed-scalar components. This contains no support compositor, no composite-map
projection and no composition-coherence assertion.

Source: fix-prop-projection-formula.proof.md, coefficient transport in the composition
sentence; naturality of projectionMapOfCompactification and coefficient units
(blueprint: lem-sf-finite-projection-iteration-realization).

Proof: expand the two components as source comparison, realized fixed component,
and inverse target comparison. Naturality of the outer support realization moves
its image of the inner component past that realization. The intermediate coefficient
unit cancels with its inverse. Naturality of the outer fixed projection in its first
input moves fixedSupportRealization for f to the source. Naturality of the inner
fixed projection in its second input moves fixedPullRealization for g to the target.
The remaining target is precisely iterationTensorComparison followed by the two
support realizations. Functoriality and associativity give the displayed equation.
The argument uses neither boundedness beyond the stated domains nor invertibility
of a projection, and applies to zero objects and identity maps without exceptions. -/
theorem iteration_realization :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
    let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
    let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
    let Pg := fixedDerivedPull (C := C) (E := E) (n := n) g
    let k := RX.inverse.obj K.obj
    let l := RZ.inverse.obj L.obj
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
    I.map (component S g cg ((S.finite.support f cf).obj K) L ≫
        (S.finite.support g cg).map (component S f cf K ((torPull S g).obj L))) ≫
      (iterationTargetComparison S f g cf cg K L).hom =
    (iterationSourceComparison S f g cf cg K L).hom ≫
      RZ.functor.map
        (fixedComponent (C := C) (E := E) (n := n) (hn := hn) g cg
          ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf).obj k) l ≫
          G.map (fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k
            (Pg.obj l))) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let RX := realization (C := C) (E := E) (n := n) (hn := hn) X
  let RY := realization (C := C) (E := E) (n := n) (hn := hn) Y
  let RZ := realization (C := C) (E := E) (n := n) (hn := hn) Z
  let IZ := (intrinsicFiniteTorsionConstructible C.l E n hn Z.obj.left).ι
  let F := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cf
  let G := sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) cg
  let TX := fixedTensor (C := C) (E := E) (n := n) X
  let TY := fixedTensor (C := C) (E := E) (n := n) Y
  let TZ := fixedTensor (C := C) (E := E) (n := n) Z
  let Pf := fixedDerivedPull (C := C) (E := E) (n := n) f
  let Pg := fixedDerivedPull (C := C) (E := E) (n := n) g
  let k := RX.inverse.obj K.obj
  let l := RZ.inverse.obj L.obj
  let M := ((partialTensor S X).obj K).obj ((torPull S f).obj ((torPull S g).obj L))
  let rho := component S g cg ((S.finite.support f cf).obj K) L ≫
    (S.finite.support g cg).map (component S f cf K ((torPull S g).obj L))
  let pf := fixedComponent (C := C) (E := E) (n := n) (hn := hn) f cf k (Pg.obj l)
  let pg := fixedComponent (C := C) (E := E) (n := n) (hn := hn) g cg (F.obj k) l
  have hf := map_three_eq G (fixed_component_realization S f cf K ((torPull S g).obj L))
  have hg := split_map_tail G
    (fixed_component_realization S g cg ((S.finite.support f cf).obj K) L)
  have hs := fixed_support_naturality S g cg (component S f cf K ((torPull S g).obj L))
  have hnf := map_two_eq G (fixed_projection_second_coordinates
    (C := C) (E := E) (n := n) (hn := hn) f cf k
    (fixedPullRealization S g ⟨L.obj, L.property.1⟩).hom)
  have hng := fixed_projection_first_coordinates
    (C := C) (E := E) (n := n) (hn := hn) g cg (fixedSupportRealization S f cf K).hom l
  have hty := (TY.map (fixedSupportRealization S f cf K).hom).naturality
    (fixedPullRealization S g ⟨L.obj, L.property.1⟩).hom
  have htyg := map_two_eq G hty
  have hsplit := map_unit_tensor_trans RX (F ⋙ G) TX k
    (fixedPullRealization S f
      ⟨((torPull S g).obj L).obj, ((torPull S g).obj L).property.1⟩)
    (Pf.mapIso (fixedPullRealization S g ⟨L.obj, L.property.1⟩))
  have hsplit' : G.map (F.map (iterationTensorComparison S f g K L).hom) = _ := hsplit
  have hc :
      RZ.inverse.map (IZ.map rho) ≫ (fixedSupportRealization S g cg
        ((S.finite.support f cf).obj M)).hom ≫
          G.map (fixedSupportRealization S f cf M).hom ≫
          G.map (F.map (iterationTensorComparison S f g K L).hom) =
      (RZ.unitIso.app ((TZ.obj (RZ.inverse.obj
        ((S.finite.support g cg).obj ((S.finite.support f cf).obj K)).obj)).obj l)).inv ≫
        ((TZ.map (fixedSupportRealization S g cg ((S.finite.support f cf).obj K)).hom).app
          l) ≫
        ((TZ.map (G.map (fixedSupportRealization S f cf K).hom)).app l) ≫ pg ≫ G.map pf := by
    have h := diagram_transport hs hf hg hnf htyg hng hsplit'
    exact combine_map_path (IZ ⋙ RZ.inverse)
      (component S g cg ((S.finite.support f cf).obj K) L)
      ((S.finite.support g cg).map (component S f cf K ((torPull S g).obj L))) _ _ _ h
  exact realize_of_inverse_two RZ
    (u := (TZ.obj (RZ.inverse.obj
      ((S.finite.support g cg).obj ((S.finite.support f cf).obj K)).obj)).obj l)
    (IZ.map rho)
    ((TZ.mapIso (fixedSupportRealization S g cg ((S.finite.support f cf).obj K))).app l)
    ((TZ.mapIso (G.mapIso (fixedSupportRealization S f cf K))).app l)
    (supportRealization S g cg ((S.finite.support f cf).obj M))
    (G.mapIso (fixedSupportRealization S f cf M))
    (G.mapIso (F.mapIso (iterationTensorComparison S f g K L)))
    (pg ≫ G.map pf) hc

end WeilConjectures.CompactSupportFiniteProjection
