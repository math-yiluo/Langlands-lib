/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# The Frobenius exchange isomorphisms of `φ̄^*` and `φ̄_*` are mates

Let `φ : X₀ ⟶ Y₀` be a morphism of schemes over a finite field with base change
`φ̄ : X ⟶ Y` to the geometric fibres. The exchange isomorphisms
`φ̄^* ⋙ (Fr_X⁻¹)_* ≅ (Fr_Y⁻¹)_* ⋙ φ̄^*` and `φ̄_* ⋙ (Fr_Y⁻¹)_* ≅ (Fr_X⁻¹)_* ⋙ φ̄_*` of `ℓ`-adic
sheaves are mates under the adjunction `φ̄^* ⊣ φ̄_*`
(`AlgebraicGeometry.ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_eq_mateEquiv`).
Consequently the unit and the counit of `φ̄^* ⊣ φ̄_*` are compatible with Frobenius structures,
which makes `φ^* ⊣ φ_*` an adjunction of Weil sheaves.

The proof iterates the mates correspondence along the Frobenius equivalences
`(Fr⁻¹)_* ⊣ Fr_*`: the iterated mate of the pullback exchange isomorphism is its conjugate, a
composite of composition and congruence isomorphisms of pushforwards, by the conjugation
identities for the pullbacks (`conjugateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv`);
and the mate of the pushforward exchange isomorphism along the Frobenius equivalences is the same
composite, which is checked on sections
(`AlgebraicGeometry.ProEtale.lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

section Sheaf

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The units of pushforwards along morphisms `ai`, `ah` with `ai ≫ ah = 𝟙` and `bi`, `bh` with
`bi ≫ bh = 𝟙` are compatible with the factorisation isomorphisms of commutative squares
`ah ≫ φ = φ ≫ bh` and `ai ≫ φ = φ ≫ bi`. -/
lemma lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor {X Y : Scheme.{u}} (φ : X ⟶ Y)
    {ah ai : X ⟶ X} {bh bi : Y ⟶ Y} {c d : X ⟶ Y} (ha : ai ≫ ah = 𝟙 X) (hb : bi ≫ bh = 𝟙 Y)
    (e₁ : ah ≫ φ = c) (e₂ : φ ≫ bh = c) (e₃ : φ ≫ bi = d) (e₄ : ai ≫ φ = d)
    (M : Sheaf (Scheme.ProEt.topology X) A) :
    (φ)_*[A].map ((lowerStarUnit A ha).app M) ≫ (lowerStarFactor A e₁).hom.app ((ai)_*[A].obj M) ≫
        (lowerStarFactor A e₂).inv.app ((ai)_*[A].obj M) =
      (lowerStarUnit A hb).app ((φ)_*[A].obj M) ≫
        (bh)_*[A].map ((lowerStarFactor A e₃).hom.app M ≫ (lowerStarFactor A e₄).inv.app M) := by
  ext V
  simp only [lowerStarUnit, Iso.trans_inv, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarFactor_hom_app_hom_app,
    lowerStarFactor_inv_app_hom_app, lowerStarId_inv_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map', ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackId,
    MorphismProperty.Comma.comp_left]
  apply pullback.hom_ext <;> simp [pullback.condition_assoc, ha]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composite of a composition, an identity and a congruence isomorphism of pushforwards
along `i ≫ f = 𝟙` is the unit `lowerStarUnit`. -/
lemma lowerStarComp_trans_lowerStarCongr_trans_lowerStarId_inv {X Y : Scheme.{u}} {i : X ⟶ Y}
    {f : Y ⟶ X} (h : i ≫ f = 𝟙 X) :
    (lowerStarComp A i f ≪≫ lowerStarCongr A h ≪≫ lowerStarId A X).inv = lowerStarUnit A h := by
  rw [← Iso.trans_assoc, lowerStarComp_trans_lowerStarCongr]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- An exchange isomorphism of pushforwards along a commutative square is a composite of
factorisation isomorphisms. -/
lemma lowerStarComp_trans_lowerStarCongr_trans_lowerStarComp_symm_hom {X Y Y' Z : Scheme.{u}}
    {p : X ⟶ Y} {q : Y ⟶ Z} {p' : X ⟶ Y'} {q' : Y' ⟶ Z} (e : p ≫ q = p' ≫ q') :
    (lowerStarComp A p q ≪≫ lowerStarCongr A e ≪≫ (lowerStarComp A p' q').symm).hom =
      (lowerStarFactor A e).hom ≫ (lowerStarFactor A (rfl : p' ≫ q' = p' ≫ q')).inv := by
  rw [← Iso.trans_assoc, lowerStarComp_trans_lowerStarCongr, Iso.trans_hom, Iso.symm_hom,
    ← lowerStarComp_trans_lowerStarCongr A (rfl : p' ≫ q' = p' ≫ q'), lowerStarCongr_rfl,
    Iso.trans_refl]

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)

/-- The exchange isomorphism `φ^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ φ^*` of pullbacks along a commutative
square `a ≫ φ = φ ≫ b` with `a`, `b` isomorphisms:
`(a⁻¹)_* φ^* ≅ a^* φ^* ≅ (a ≫ φ)^* = (φ ≫ b)^* ≅ φ^* b^* ≅ φ^* (b⁻¹)_*`. -/
noncomputable def upperStarExchangeIso (c : a.hom ≫ φ = φ ≫ b.hom) :
    (φ)^*[A] ⋙ (a.inv)_*[A] ≅ (b.inv)_*[A] ⋙ (φ)^*[A] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv A a).symm ≪≫ (upperStarComp A _ _).symm ≪≫
    upperStarCongr A c ≪≫ upperStarComp A _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv A b) _

/-- The exchange isomorphism `φ_* ⋙ (b⁻¹)_* ≅ (a⁻¹)_* ⋙ φ_*` of pushforwards along a commutative
square `φ ≫ b⁻¹ = a⁻¹ ≫ φ`. -/
noncomputable abbrev lowerStarExchangeIso (w : φ ≫ b.inv = a.inv ≫ φ) :
    (φ)_*[A] ⋙ (b.inv)_*[A] ≅ (a.inv)_*[A] ⋙ (φ)_*[A] :=
  lowerStarComp A _ _ ≪≫ lowerStarCongr A w ≪≫ (lowerStarComp A _ _).symm

/-- The conjugate of the pullback exchange isomorphism, under the adjunctions `φ^* ⊣ φ_*`
composed with the Frobenius-type equivalences `(a⁻¹)_* ⊣ a_*` and `(b⁻¹)_* ⊣ b_*`, is the
pushforward exchange isomorphism `a_* ⋙ φ_* ≅ (a ≫ φ)_* = (φ ≫ b)_* ≅ φ_* ⋙ b_*`. Each of its
five constituents is conjugate to an identity, a composition or a congruence isomorphism of
pushforwards. -/
lemma conjugateEquiv_upperStarExchangeIso_inv (c : a.hom ≫ φ = φ ≫ b.hom) :
    conjugateEquiv ((upperStarLowerStarAdjunction A φ).comp
        (lowerStarEquivalence A a).symm.toAdjunction)
      ((lowerStarEquivalence A b).symm.toAdjunction.comp (upperStarLowerStarAdjunction A φ))
      (upperStarExchangeIso A φ a b c).inv =
    (lowerStarComp A a.hom φ ≪≫ lowerStarCongr A c ≪≫ (lowerStarComp A φ b.hom).symm).hom := by
  set adj := upperStarLowerStarAdjunction A φ
  have h₁ := conjugateEquiv_whiskerRight (upperStarLowerStarAdjunction A b.hom)
    (lowerStarEquivalence A b).symm.toAdjunction adj (upperStarIsoLowerStarInv A b).inv
  have h₂ := conjugateEquiv_upperStarComp_inv A φ b.hom
  have h₃ := conjugateEquiv_upperStarCongr_inv A c
  have h₄ := conjugateEquiv_upperStarComp_hom A a.hom φ
  have h₅ := conjugateEquiv_whiskerLeft (lowerStarEquivalence A a).symm.toAdjunction
    (upperStarLowerStarAdjunction A a.hom) adj (upperStarIsoLowerStarInv A a).hom
  have hb : conjugateEquiv (upperStarLowerStarAdjunction A b.hom)
      (lowerStarEquivalence A b).symm.toAdjunction (upperStarIsoLowerStarInv A b).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have ha : conjugateEquiv (lowerStarEquivalence A a).symm.toAdjunction
      (upperStarLowerStarAdjunction A a.hom) (upperStarIsoLowerStarInv A a).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [hb] at h₁
  rw [ha] at h₅
  simp only [upperStarExchangeIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ ((upperStarLowerStarAdjunction A b.hom).comp adj) _,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (φ ≫ b.hom)) _,
    ← conjugateEquiv_comp _ (upperStarLowerStarAdjunction A (a.hom ≫ φ)) _,
    ← conjugateEquiv_comp _ (adj.comp (upperStarLowerStarAdjunction A a.hom)) _]
  rw [h₁, h₂, h₃, h₄, h₅]
  simp only [Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.comp_id,
    Category.id_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The unit of the adjunction `(e⁻¹)_* ⊣ e_*` underlying the equivalence `e_*` is
`lowerStarUnit`. -/
lemma lowerStarEquivalence_symm_toAdjunction_unit {Z W : Scheme.{u}} (e : Z ≅ W) :
    (lowerStarEquivalence A e).symm.toAdjunction.unit = lowerStarUnit A e.inv_hom_id :=
  lowerStarComp_trans_lowerStarCongr_trans_lowerStarId_inv A e.inv_hom_id

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The mate of the pushforward exchange isomorphism along `φ ≫ b⁻¹ = a⁻¹ ≫ φ` under the
adjunctions `(a⁻¹)_* ⊣ a_*` and `(b⁻¹)_* ⊣ b_*` is the pushforward exchange isomorphism along
`a ≫ φ = φ ≫ b`. -/
lemma mateEquiv_lowerStarExchangeIso_hom (w : φ ≫ b.inv = a.inv ≫ φ)
    (c : a.hom ≫ φ = φ ≫ b.hom) :
    mateEquiv (lowerStarEquivalence A a).symm.toAdjunction
        (lowerStarEquivalence A b).symm.toAdjunction
        (TwoSquare.mk _ _ _ _ (lowerStarExchangeIso A φ a b w).hom) =
      TwoSquare.mk _ _ _ _
        (lowerStarComp A a.hom φ ≪≫ lowerStarCongr A c ≪≫ (lowerStarComp A φ b.hom).symm).hom := by
  refine mateEquiv_eq_of_unit _ _ _ _ fun M ↦ ?_
  rw [lowerStarEquivalence_symm_toAdjunction_unit, lowerStarEquivalence_symm_toAdjunction_unit]
  have h₁ := congrArg (fun e ↦ e.app ((a.inv)_*[A].obj M))
    (lowerStarComp_trans_lowerStarCongr_trans_lowerStarComp_symm_hom A c)
  have h₂ := congrArg (fun e ↦ e.app M)
    (lowerStarComp_trans_lowerStarCongr_trans_lowerStarComp_symm_hom A w)
  simp only [NatTrans.comp_app] at h₁ h₂
  change (φ)_*[A].map ((lowerStarUnit A a.inv_hom_id).app M) ≫
      (lowerStarComp A a.hom φ ≪≫ lowerStarCongr A c ≪≫
        (lowerStarComp A φ b.hom).symm).hom.app ((a.inv)_*[A].obj M) =
    (lowerStarUnit A b.inv_hom_id).app ((φ)_*[A].obj M) ≫
      (b.hom)_*[A].map ((lowerStarExchangeIso A φ a b w).hom.app M)
  rw [h₁, h₂]
  exact lowerStar_map_lowerStarUnit_app_comp_lowerStarFactor A φ a.inv_hom_id b.inv_hom_id c rfl
    w rfl M

/-- **The Frobenius exchange isomorphisms of `φ^*` and `φ_*` are mates.** Under the adjunction
`φ^* ⊣ φ_*`, the mate of the inverse of the pullback exchange isomorphism along `a ≫ φ = φ ≫ b`
is the pushforward exchange isomorphism along `φ ≫ b⁻¹ = a⁻¹ ≫ φ`. Iterating the mates
correspondence along `(a⁻¹)_* ⊣ a_*` and `(b⁻¹)_* ⊣ b_*` turns both sides into the same
pushforward exchange isomorphism (`conjugateEquiv_upperStarExchangeIso_inv`,
`mateEquiv_lowerStarExchangeIso_hom`). -/
lemma mateEquiv_upperStarExchangeIso_inv (w : φ ≫ b.inv = a.inv ≫ φ)
    (c : a.hom ≫ φ = φ ≫ b.hom) :
    mateEquiv (upperStarLowerStarAdjunction A φ) (upperStarLowerStarAdjunction A φ)
        (TwoSquare.mk _ _ _ _ (upperStarExchangeIso A φ a b c).inv) =
      TwoSquare.mk _ _ _ _ (lowerStarExchangeIso A φ a b w).hom := by
  apply (mateEquiv (lowerStarEquivalence A a).symm.toAdjunction
    (lowerStarEquivalence A b).symm.toAdjunction).injective
  refine (iterated_mateEquiv_conjugateEquiv _ _ _ _ _).trans ?_
  rw [conjugateEquiv_upperStarExchangeIso_inv, mateEquiv_lowerStarExchangeIso_hom A φ a b w c]

end Sheaf

end AlgebraicGeometry.ProEtale
