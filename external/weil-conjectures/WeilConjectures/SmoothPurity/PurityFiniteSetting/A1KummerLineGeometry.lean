/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Polynomial spectra and the actual relative affine line
Source: det-prop-a1-kummer.proof.md, Reduction to a geometric fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PurityFiniteSetting

/-- The polynomial model is the actual affine line, by the one-variable algebra equivalence.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry). -/
noncomputable def a1KummerAbsoluteLineIso (k : Type u) [Field k] :
    AlgebraicGeometry.KummerLine.curve k false ≅ Line (Spec (.of k)) :=
  Scheme.Spec.mapIso
    (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).symm

/-- The polynomial-line identification is over the ground field.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry).
Proof: the one-variable algebra equivalence fixes scalar constants. -/
theorem a1KummerAbsoluteLineIso_over (k : Type u) [Field k] :
    (a1KummerAbsoluteLineIso k).hom ≫ lineProjection (Spec (.of k)) =
      AlgebraicGeometry.KummerLine.structureMap k false := by
  dsimp only [a1KummerAbsoluteLineIso, Iso.trans_hom, Iso.symm_hom,
    lineProjection, Line]
  rw [Category.assoc, AffineSpace.SpecIso_inv_over]
  change Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingHom) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) =
    Spec.map (CommRingCat.ofHom Polynomial.C)
  rw [← Spec.map_comp]
  congr 1
  ext a n
  exact congrArg (fun p : Polynomial k ↦ p.coeff n)
    ((MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).commutes a)

/-- The actual affine coordinate pulls back to the polynomial variable.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry).
Proof: apply naturality of global functions of Spec to the variable, using that the
one-variable algebra equivalence sends the unique multivariable variable to X. -/
theorem a1KummerAbsoluteLineIso_coordinate (k : Type u) [Field k] :
    (a1KummerAbsoluteLineIso k).hom.appTop (coordinate (Spec (.of k))) =
      (Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X := by
  change (Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv).appTop
        (AffineSpace.coord (Spec (.of k)) (ULift.up 0)) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.SpecIso_inv_appTop_coord]
  have h := congrArg (fun f : CommRingCat.of
      (MvPolynomial (ULift.{u} (Fin 1)) k) ⟶ Γ(Spec (.of (Polynomial k)), ⊤) ↦
      f (MvPolynomial.X (ULift.up 0)))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingHom))
  change (Scheme.ΓSpecIso (.of (Polynomial k))).inv
      ((MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1)))
        (MvPolynomial.X (ULift.up 0))) =
    (Spec.map (CommRingCat.ofHom
      (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv
          (MvPolynomial.X (ULift.up 0))) at h
  rw [show (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1)))
      (MvPolynomial.X (ULift.up 0)) = Polynomial.X by
    simp [MvPolynomial.uniqueAlgEquiv_apply]] at h
  exact h.symm

/-- The actual affine line is the polynomial family's pullback square.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry).
Proof: transport the affine-space pullback square along the absolute polynomial-line
isomorphism. Its scalar compatibility is the previously proved over-base identity. -/
theorem a1KummerLine_isPullback {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    IsPullback
      (AffineSpace.map (n := ULift.{u} (Fin 1)) a ≫ (a1KummerAbsoluteLineIso k).inv)
      (lineProjection Y) (AlgebraicGeometry.KummerLine.structureMap k false) a := by
  apply (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) a).of_iso
    (Iso.refl _) (a1KummerAbsoluteLineIso k).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp [lineProjection]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← a1KummerAbsoluteLineIso_over, Iso.inv_hom_id_assoc]
    rfl
  · simp

/-- The canonical pullback-presentation isomorphism, determined by its two projections.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry). -/
noncomputable def a1KummerLineFamilyIso {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    pullback (AlgebraicGeometry.KummerLine.structureMap k false) a ≅ Line Y :=
  (a1KummerLine_isPullback a).isoPullback.symm

/-- The family isomorphism preserves the projection and the actual coordinate.
Source: det-prop-a1-kummer.proof.md (blueprint: new-pur-a1-kummer-line-geometry).
Proof: the universal pullback isomorphism preserves both projections. The affine-space
map preserves its coordinate; the absolute comparison sends it to X. Apply appTop to
the first-projection identity and compose these two coordinate identities. -/
theorem a1KummerLineFamilyIso_normalization {k : Type u} [Field k] {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of k)) :
    (a1KummerLineFamilyIso a).hom ≫ lineProjection Y =
        pullback.snd (AlgebraicGeometry.KummerLine.structureMap k false) a ∧
    (a1KummerLineFamilyIso a).hom.appTop (coordinate Y) =
      (pullback.fst (AlgebraicGeometry.KummerLine.structureMap k false) a).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) := by
  constructor
  · exact (a1KummerLine_isPullback a).isoPullback_inv_snd
  · have hf : (a1KummerLineFamilyIso a).hom ≫
          AffineSpace.map (n := ULift.{u} (Fin 1)) a =
        pullback.fst (AlgebraicGeometry.KummerLine.structureMap k false) a ≫
          (a1KummerAbsoluteLineIso k).hom := by
      rw [← cancel_mono (a1KummerAbsoluteLineIso k).inv]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact (a1KummerLine_isPullback a).isoPullback_inv_fst
    calc
      _ = ((a1KummerLineFamilyIso a).hom ≫
          AffineSpace.map (n := ULift.{u} (Fin 1)) a).appTop
            (coordinate (Spec (.of k))) := by
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact congrArg (a1KummerLineFamilyIso a).hom.appTop
          (AffineSpace.map_appTop_coord a (ULift.up 0)).symm
      _ = _ := by
        rw [hf, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        exact congrArg
          (pullback.fst (AlgebraicGeometry.KummerLine.structureMap k false) a).appTop
          (a1KummerAbsoluteLineIso_coordinate k)

/-- The actual punctured-line square is cartesian for every base map.
Source: det-prop-a1-kummer.proof.md, Base change on Y
(blueprint: new-pur-a1-kummer-line-geometry).
Proof: the affine-space map pulls the coordinate back to the coordinate, hence its
inverse image of the coordinate basic open is the coordinate basic open. The open
immersion pullback criterion gives the open square; paste with the affine-line square. -/
theorem a1KummerPunctured_isPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsPullback (puncturedMap f) (puncturedProjection X) (puncturedProjection Y) f := by
  have : IsOpenImmersion (openImmersion X) := by
    dsimp only [openImmersion]
    infer_instance
  have : IsOpenImmersion (openImmersion Y) := by
    dsimp only [openImmersion]
    infer_instance
  have ho : IsPullback (puncturedMap f) (openImmersion X) (openImmersion Y)
      (AffineSpace.map (n := ULift.{u} (Fin 1)) f) := by
    apply IsOpenImmersion.isPullback
    · exact (Classical.choose_spec (existsUnique_puncturedMap f)).1.symm
    · change AffineSpace.map (n := ULift.{u} (Fin 1)) f ⁻¹ᵁ
        ((Line Y).basicOpen (coordinate Y)).ι.opensRange =
          ((Line X).basicOpen (coordinate X)).ι.opensRange
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
      dsimp only [Line, coordinate]
      rw [Scheme.preimage_basicOpen_top, AffineSpace.map_appTop_coord]
  exact ho.paste_vert (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) f)

/-- The actual punctured-line map preserves the actual coordinate unit.
Source: det-prop-a1-kummer.proof.md, Base change on Y
(blueprint: new-pur-a1-kummer-line-geometry).
Proof: take global sections of the defining equality with the open immersions and
use preservation of the affine coordinate. Units are determined by their values. -/
theorem a1KummerPuncturedMap_coordinate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Units.map (puncturedMap f).appTop.hom.toMonoidHom (coordinateUnit Y) =
      coordinateUnit X := by
  apply Units.ext
  change (puncturedMap f).appTop
      ((Line Y).isUnit_ι_appTop_basicOpen (coordinate Y)).unit.val =
    ((Line X).isUnit_ι_appTop_basicOpen (coordinate X)).unit.val
  rw [IsUnit.unit_spec, IsUnit.unit_spec]
  have h := congrArg (fun g : Punctured X ⟶ Line Y ↦ g.appTop (coordinate Y))
    (Classical.choose_spec (existsUnique_puncturedMap f)).1
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact h.trans (congrArg (openImmersion X).appTop
    (AffineSpace.map_appTop_coord f (ULift.up 0)))

end WeilConjectures.PurityFiniteSetting
