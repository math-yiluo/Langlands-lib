/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Composition

/-!
# The canonical composition isomorphism in a compact support formalism

For a compact support formalism `F` satisfying proper base change, and morphisms admitting
compactifications, `F.lowerShriek f` is the compactly supported direct image along the chosen
compactification of `f`. This file defines the composition isomorphism

`F.lowerShriekCompIso f g : F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g)`

of blueprint `proposition-composition-base-change-rf-shriek--1` and proves that

- it is computed by any triangle of compactifications, up to the comparison isomorphisms
  `F.shriekIso` (`lowerShriekCompIso_hom_eq`): it is independent of all compactification
  choices;
- it is the identity when `f` or `g` is an identity (`lowerShriekCompIso_id_left`,
  `lowerShriekCompIso_id_right`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u})

variable {X Y S : Scheme.{u}}

/-- The compactly supported direct image along `f`, computed with the chosen compactification
`AlgebraicGeometry.HasCompactification.compactification f`. -/
noncomputable abbrev lowerShriek (f : X ⟶ Y) [HasCompactification f] : F.obj X ⥤ F.obj Y :=
  F.shriek (HasCompactification.compactification f)

/-- The isomorphism `F.lowerShriek f ≅ F.lowerShriek f'` for `f = f'`. -/
noncomputable def lowerShriekCongr {f f' : X ⟶ Y} [HasCompactification f]
    [HasCompactification f'] (h : f = f') : F.lowerShriek f ≅ F.lowerShriek f' := by
  subst h
  exact Iso.refl _

@[simp]
lemma lowerShriekCongr_refl (f : X ⟶ Y) [HasCompactification f] :
    F.lowerShriekCongr (rfl : f = f) = Iso.refl _ :=
  rfl

variable [F.HasProperExchange]

/-- The comparison isomorphism between a copy of the chosen compactification of `f` and the
chosen compactification of `f'`, for `f' = f`, is `F.lowerShriekCongr`. -/
lemma shriekIso_copy {f f' : X ⟶ Y} [HasCompactification f] [HasCompactification f']
    [QuasiCompact f'] (h : f' = f) :
    F.shriekIso ((HasCompactification.compactification f).copy h)
        (HasCompactification.compactification f') = F.lowerShriekCongr h.symm := by
  subst h
  exact F.shriekIso_refl _

/-- **The composition isomorphism** `F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g)`
for morphisms admitting compactifications with quasi-compact composite: the composition
isomorphism of the triangle `Compactification.Triangle.ofHasCompactification f g`, compared with
the chosen compactifications. (blueprint: `proposition-composition-base-change-rf-shriek--1`) -/
noncomputable def lowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)] :
    F.lowerShriek f ⋙ F.lowerShriek g ≅ F.lowerShriek (f ≫ g) :=
  have : QuasiCompact f := .of_comp f g
  Functor.isoWhiskerRight
      (F.shriekIso _ (Compactification.Triangle.ofHasCompactification f g).cf) _ ≪≫
    F.compIso (Compactification.Triangle.ofHasCompactification f g) ≪≫ F.shriekIso _ _

/-- **Independence of all compactification choices**: the composition isomorphism is computed
by any triangle of compactifications `T` of `(f, g)`, up to the comparison isomorphisms
`F.shriekIso` between the compactifications of `T` and the chosen ones.
(blueprint: `proposition-composition-base-change-rf-shriek--1`, via
`proposition-construction-independence-rf-shriek`) -/
theorem lowerShriekCompIso_hom_eq {f : X ⟶ Y} {g : Y ⟶ S} [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact f] [QuasiCompact g]
    [QuasiCompact (f ≫ g)] (T : Compactification.Triangle f g) :
    (F.lowerShriekCompIso f g).hom =
      NatTrans.hcomp (F.shriekIso _ T.cf).hom (F.shriekIso _ T.cg).hom ≫
        (F.compIso T).hom ≫ (F.shriekIso T.cfg _).hom := by
  rw [lowerShriekCompIso, Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    F.compIso_hom_eq _ T, ← Functor.hcomp_id]
  simp only [Category.assoc]
  rw [← Category.assoc (NatTrans.hcomp _ _), ← NatTrans.exchange, Category.id_comp]
  have h₁ := congrArg Iso.hom (F.shriekIso_trans (HasCompactification.compactification f)
    (Compactification.Triangle.ofHasCompactification f g).cf T.cf)
  have h₂ := congrArg Iso.hom (F.shriekIso_trans T.cfg
    (Compactification.Triangle.ofHasCompactification f g).cfg
    (HasCompactification.compactification (f ≫ g)))
  simp only [Iso.trans_hom] at h₁ h₂
  rw [h₁, h₂]
  rfl

/-- The identification `F.lowerShriek (𝟙 X) ≅ 𝟭`. -/
noncomputable def lowerShriekId (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    F.lowerShriek (𝟙 X) ≅ 𝟭 _ :=
  F.shriekIso _ (Compactification.ofIsProper (𝟙 X)) ≪≫ F.shriekOfIsProperIdIso X

/-- **The left unit law** of the composition isomorphism.
(blueprint: `proposition-composition-base-change-rf-shriek--1`) -/
theorem lowerShriekCompIso_id_left (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 X)] [HasCompactification (𝟙 X ≫ f)] [QuasiCompact f] :
    (F.lowerShriekCompIso (𝟙 X) f).hom =
      Functor.whiskerRight (F.lowerShriekId X).hom _ ≫ (Functor.leftUnitor _).hom ≫
        (F.lowerShriekCongr (Category.id_comp f).symm).hom := by
  rw [F.lowerShriekCompIso_hom_eq
      (Compactification.Triangle.unitLeft (HasCompactification.compactification f)),
    compIso_unitLeft]
  change NatTrans.hcomp (F.shriekIso _ (Compactification.ofIsProper (𝟙 X))).hom
      (F.shriekIso (HasCompactification.compactification f)
        (HasCompactification.compactification f)).hom ≫
      (Functor.whiskerRight (F.shriekOfIsProperIdIso X).hom _ ≫ (Functor.leftUnitor _).hom) ≫
      (F.shriekIso ((HasCompactification.compactification f).copy (Category.id_comp f))
        (HasCompactification.compactification (𝟙 X ≫ f))).hom = _
  rw [shriekIso_refl, F.shriekIso_copy (Category.id_comp f), lowerShriekId, Iso.trans_hom,
    Functor.whiskerRight_comp, ← Functor.hcomp_id, ← Functor.hcomp_id]
  simp only [Iso.refl_hom, Category.assoc]

/-- **The right unit law** of the composition isomorphism.
(blueprint: `proposition-composition-base-change-rf-shriek--1`) -/
theorem lowerShriekCompIso_id_right (f : X ⟶ Y) [HasCompactification f]
    [HasCompactification (𝟙 Y)] [HasCompactification (f ≫ 𝟙 Y)] [QuasiCompact f] :
    (F.lowerShriekCompIso f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (F.lowerShriekId Y).hom ≫ (Functor.rightUnitor _).hom ≫
        (F.lowerShriekCongr (Category.comp_id f).symm).hom := by
  rw [F.lowerShriekCompIso_hom_eq
      (Compactification.Triangle.unitRight (HasCompactification.compactification f)),
    compIso_unitRight]
  change NatTrans.hcomp (F.shriekIso (HasCompactification.compactification f)
        (HasCompactification.compactification f)).hom
      (F.shriekIso _ (Compactification.ofIsProper (𝟙 Y))).hom ≫
      (Functor.whiskerLeft _ (F.shriekOfIsProperIdIso Y).hom ≫ (Functor.rightUnitor _).hom) ≫
      (F.shriekIso ((HasCompactification.compactification f).copy (Category.comp_id f))
        (HasCompactification.compactification (f ≫ 𝟙 Y))).hom = _
  rw [shriekIso_refl, F.shriekIso_copy (Category.comp_id f), lowerShriekId, Iso.trans_hom,
    Functor.whiskerLeft_comp, ← Functor.id_hcomp, ← Functor.id_hcomp]
  simp only [Iso.refl_hom, Category.assoc]

end AlgebraicGeometry.CompactSupportFormalism
