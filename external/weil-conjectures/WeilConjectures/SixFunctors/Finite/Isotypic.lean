/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.AddChar
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.ConstantSheafEnd

/-!
# Isotypic components of `f_* Λ` for a finite covering with a group action

Let `f : Y ⟶ X` be a finite morphism and let a finite abelian group `G` act on `Y` over `X`
through endomorphisms `τ_g`, so that `τ_g ≫ f = f` and `τ_{a + b} = τ_a ≫ τ_b`. Pulling back
sections along `τ_g` makes `G` act on the pushforward `f_* Λ` of the constant sheaf. For a
character `χ` of `G` with `|G|` invertible in `Λ`, the endomorphism
`e_χ = |G|⁻¹ ∑_g χ(-g) τ_g^♯` of `f_* Λ` is an idempotent cutting out the `χ`-isotypic
component.

If `G` acts transitively on the geometric fibres of `f`, a morphism `φ : F ⟶ f_* Λ` on which
`G` acts through `χ`, and whose adjoint `f^* F ⟶ Λ` is an isomorphism, identifies `F` with the
isotypic component. In particular two such sheaves are isomorphic as soon as `f` is surjective.
This is how the Artin–Schreier sheaf and its relatives are compared: a sheaf which becomes
trivial on the covering `f`, with descent datum given by `χ`, is determined by `χ`.

## Main definitions

- `AlgebraicGeometry.Etale.isotypicIdempotent`: the idempotent `e_χ` of `f_* Λ`.

## Main results

- `AlgebraicGeometry.Etale.isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent`: for
  `φ : F ⟶ f_* Λ` of type `χ` with invertible adjoint, `f^*` of the induced morphism from `F`
  to the image of `e_χ` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`: for `f` surjective, two sheaves with
  such morphisms to `f_* Λ` are isomorphic.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section Stalk

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω]
  [IsAlgClosed Ω]

/-- The stalk at a geometric point `s` of the adjoint `f^* F ⟶ G` of a morphism
`φ : F ⟶ f_* G` is the stalk of `φ` at `s ≫ f` followed by the restriction of germs to `s`. -/
lemma sheafFiber_map_upperStar_map_comp_counit (s : Spec (.of Ω) ⟶ Y)
    {F : Sheaf X.smallEtaleTopology A} {G : Sheaf Y.smallEtaleTopology A}
    (φ : F ⟶ (f)_*[A].obj G) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((f)^*[A].map φ ≫ (upperStarLowerStarAdjunction A f).counit.app G) =
      (upperStarCompSheafFiberIso A f s).hom.app F ≫
        (Scheme.pointSmallEtale (s ≫ f)).sheafFiber.map φ ≫
          Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G := by
  have h := (upperStarCompSheafFiberIso A f s).inv.naturality φ
  simp only [Functor.comp_map] at h
  rw [Etale.stalkRestrict_eq_counit, reassoc_of% h, Iso.hom_inv_id_app_assoc,
    Functor.map_comp]

end Stalk

/-- On the stalk at `s ≫ g`, the unit `ε : Λ ⟶ g_* Λ` followed by the restriction of germs to
`s` is an isomorphism `Λ_{s ≫ g} ≅ Λ_s`: it is the stalk at `s` of the unit isomorphism
`g^* Λ ≅ Λ`. -/
instance isIso_sheafFiber_map_ε_comp_stalkRestrict {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    IsIso ((Scheme.pointSmallEtale (s ≫ g)).sheafFiber.map
        (Functor.LaxMonoidal.ε (g)_*[ModuleCat.{u + 1} Λ]) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) g (s ≫ g) ⟨s, rfl⟩ (𝟙_ _)) := by
  have h := sheafFiber_map_upperStar_map_comp_counit (ModuleCat.{u + 1} Λ) g s
    (Functor.LaxMonoidal.ε (g)_*[ModuleCat.{u + 1} Λ])
  rw [Adjunction.map_ε_comp_counit_app_unit] at h
  have : IsIso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g s).hom.app (𝟙_ _) ≫
      (Scheme.pointSmallEtale (s ≫ g)).sheafFiber.map
        (Functor.LaxMonoidal.ε (g)_*[ModuleCat.{u + 1} Λ]) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) g (s ≫ g) ⟨s, rfl⟩ (𝟙_ _)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((upperStarCompSheafFiberIso _ g s).hom.app (𝟙_ _)) _

section Idempotent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {G : Type*} [AddCommGroup G] [Fintype G]
  (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ f = f)

omit [Fintype G] in
include hτ in
/-- `G` acts on `f_* Λ`: `τ_{a + b}^♯ = τ_a^♯ ≫ τ_b^♯`. -/
lemma lowerStarConstantSheafEndOfOver_add (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b) (a b : G) :
    lowerStarConstantSheafEndOfOver (Λ := Λ) f (τ (a + b)) (hτ _) =
      lowerStarConstantSheafEndOfOver f (τ a) (hτ a) ≫
        lowerStarConstantSheafEndOfOver f (τ b) (hτ b) :=
  lowerStarConstantSheafEndOfOver_of_eq_comp _ _ _ _ (by rw [add_comm, hadd]) _ _ _

variable [Invertible (Fintype.card G : Λ)] (χ : AddChar G Λ)

/-- The endomorphism `e_χ = |G|⁻¹ ∑_g χ(-g) τ_g^♯` of `f_* Λ` cutting out the `χ`-isotypic
component. -/
def isotypicIdempotent : (f)_*[ModuleCat Λ].obj (𝟙_ _) ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _) :=
  ∑ g : G, (⅟(Fintype.card G : Λ) * χ (-g)) • lowerStarConstantSheafEndOfOver f (τ g) (hτ g)

/-- A morphism into `f_* Λ` on which `G` acts through `χ` is fixed by `e_χ`. -/
lemma comp_isotypicIdempotent {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _))
    (hφ : ∀ g, φ ≫ lowerStarConstantSheafEndOfOver f (τ g) (hτ g) = χ g • φ) :
    φ ≫ isotypicIdempotent f τ hτ χ = φ := by
  simp only [isotypicIdempotent, Preadditive.comp_sum, Linear.comp_smul, hφ, smul_smul]
  have h (g : G) : ⅟(Fintype.card G : Λ) * χ (-g) * χ g = ⅟(Fintype.card G : Λ) := by
    rw [mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Λ, smul_smul,
    mul_invOf_self, one_smul]

variable (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b)

include hadd in
/-- Each `τ_b^♯` acts on the image of `e_χ` by the scalar `χ(b)`. -/
lemma isotypicIdempotent_comp (b : G) :
    isotypicIdempotent f τ hτ χ ≫ lowerStarConstantSheafEndOfOver f (τ b) (hτ b) =
      χ b • isotypicIdempotent f τ hτ χ := by
  simp only [isotypicIdempotent, Preadditive.sum_comp, Linear.smul_comp,
    ← lowerStarConstantSheafEndOfOver_add f τ hτ hadd, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_addRight, neg_add_rev]
  congr 1
  have h : χ b * χ (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [AddChar.map_add_eq_mul]
  linear_combination (-(⅟(Fintype.card G : Λ) * χ (-a))) * h

include hadd in
/-- `e_χ` is an idempotent. -/
lemma isotypicIdempotent_comp_self :
    isotypicIdempotent f τ hτ χ ≫ isotypicIdempotent f τ hτ χ = isotypicIdempotent f τ hτ χ :=
  comp_isotypicIdempotent f τ hτ χ _ (isotypicIdempotent_comp f τ hτ χ hadd)

include hadd in
@[reassoc (attr := simp)]
lemma image_ι_comp_factorThruImage_isotypicIdempotent :
    image.ι (isotypicIdempotent f τ hτ χ) ≫ factorThruImage (isotypicIdempotent f τ hτ χ) =
      𝟙 _ := by
  rw [← cancel_mono (image.ι _), ← cancel_epi (factorThruImage _)]
  simp only [Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
  exact isotypicIdempotent_comp_self f τ hτ χ hadd

include hadd in
/-- Each `τ_b^♯` acts on the image of `e_χ` by the scalar `χ(b)`. -/
lemma image_ι_isotypicIdempotent_comp (b : G) :
    image.ι (isotypicIdempotent f τ hτ χ) ≫ lowerStarConstantSheafEndOfOver f (τ b) (hτ b) =
      χ b • image.ι (isotypicIdempotent f τ hτ χ) := by
  rw [← cancel_epi (factorThruImage (isotypicIdempotent f τ hτ χ)), image.fac_assoc,
    Linear.comp_smul, image.fac, isotypicIdempotent_comp f τ hτ χ hadd]

end Idempotent

section Finite

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] {G : Type*} [AddCommGroup G] [Fintype G]
  (τ : G → (Y ⟶ Y)) (hτ : ∀ g, τ g ≫ f = f) [∀ g, IsFinite (τ g)]
  [Invertible (Fintype.card G : Λ)] (χ : AddChar G Λ) (hadd : ∀ a b, τ (a + b) = τ a ≫ τ b)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

omit [AddCommGroup G] [Fintype G] in
/-- On the stalk at `y`, `τ_g^♯` followed by the restriction to a point `t` of the geometric
fibre factors through the restriction to `t ≫ τ_g`. -/
lemma exists_sheafFiber_map_lowerStarConstantSheafEndOfOver_comp_stalkRestrict
    (y : Spec (.of Ω) ⟶ X) (g : G) (t t' : Scheme.Hom.GeometricFiber f y)
    (h : t'.1 = t.1 ≫ τ g) :
    ∃ θ, (Scheme.pointSmallEtale y).sheafFiber.map
        (lowerStarConstantSheafEndOfOver (Λ := Λ) f (τ g) (hτ g)) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t (𝟙_ _) =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t' (𝟙_ _) ≫ θ := by
  obtain ⟨t', ht'⟩ := t'
  subst h
  exact ⟨_, Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict _ _ _ y t⟩

include hadd in
/-- If `G` acts transitively on the geometric fibre of `f` over `y`, a germ of the `χ`-isotypic
component of `f_* Λ` at `y` is determined by its value at a single point `s` of the fibre. -/
lemma mono_sheafFiber_map_image_ι_isotypicIdempotent_comp_stalkRestrict
    (y : Spec (.of Ω) ⟶ X) (s : Scheme.Hom.GeometricFiber f y)
    (htrans : ∀ t : Scheme.Hom.GeometricFiber f y, ∃ g, s.1 = t.1 ≫ τ g) :
    Mono ((Scheme.pointSmallEtale y).sheafFiber.map (image.ι (isotypicIdempotent f τ hτ χ)) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y s (𝟙_ _)) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := (Scheme.pointSmallEtale y).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  set ρ := fun t : Scheme.Hom.GeometricFiber f y ↦
    Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f y t (𝟙_ _) with hρ
  set ι := image.ι (isotypicIdempotent f τ hτ χ)
  set r := factorThruImage (isotypicIdempotent f τ hτ χ)
  have hι (b : G) : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map
        (lowerStarConstantSheafEndOfOver f (τ b) (hτ b)) =
        χ b • (Scheme.pointSmallEtale y).sheafFiber.map ι := by
    rw [← CategoryTheory.Functor.map_comp, image_ι_isotypicIdempotent_comp f τ hτ χ hadd,
      GrothendieckTopology.Point.sheafFiber_map_smul]
  have hιr : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp,
      image_ι_comp_factorThruImage_isotypicIdempotent f τ hτ χ hadd,
      CategoryTheory.Functor.map_id]
  refine Preadditive.mono_of_cancel_zero _ fun {Z} u hu ↦ ?_
  have h1 : u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι = 0 := by
    rw [← cancel_mono (Pi.lift ρ), zero_comp]
    refine Pi.hom_ext _ _ fun t ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, zero_comp]
    obtain ⟨g, hg⟩ := htrans t
    obtain ⟨θ, hθ⟩ := exists_sheafFiber_map_lowerStarConstantSheafEndOfOver_comp_stalkRestrict
      (Λ := Λ) f τ hτ y g t s hg
    have h2 : χ g • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) = 0 := by
      rw [← Linear.comp_smul, ← Linear.smul_comp, ← hι, Category.assoc, hθ]
      simp only [← Category.assoc] at hu ⊢
      rw [hu, zero_comp]
    have h3 : χ (-g) • χ g • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) =
        u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t := by
      rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        one_smul]
    rw [Category.assoc, ← h3, h2, smul_zero]
  calc u = u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
        (Scheme.pointSmallEtale y).sheafFiber.map r := by rw [hιr, Category.comp_id]
    _ = 0 := by rw [← Category.assoc, h1, zero_comp]

include hadd in
/-- **A sheaf trivialized by `f` with descent datum `χ` is the `χ`-isotypic component.** Let
`G` act transitively on the geometric fibres of `f`, and let `φ : F ⟶ f_* Λ` be a morphism on
which `G` acts through `χ` and whose adjoint `f^* F ⟶ Λ` is an isomorphism. Then `f^*` of the
induced morphism from `F` to the image of `e_χ` is an isomorphism. -/
theorem isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s t : Spec (.of Ω) ⟶ Y),
      s ≫ f = t ≫ f → ∃ g, s = t ≫ τ g)
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _))
    (hφ : ∀ g, φ ≫ lowerStarConstantSheafEndOfOver f (τ g) (hτ g) = χ g • φ)
    (hiso : IsIso ((f)^*[ModuleCat.{u + 1} Λ].map φ ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _))) :
    IsIso ((f)^*[ModuleCat.{u + 1} Λ].map
      (φ ≫ factorThruImage (isotypicIdempotent f τ hτ χ))) := by
  set M := (f)^*[ModuleCat.{u + 1} Λ].map (image.ι (isotypicIdempotent f τ hτ χ)) ≫
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _) with hM
  have hfac : (f)^*[ModuleCat.{u + 1} Λ].map
      (φ ≫ factorThruImage (isotypicIdempotent f τ hτ χ)) ≫ M =
      (f)^*[ModuleCat.{u + 1} Λ].map φ ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _) := by
    rw [hM, ← Category.assoc, ← Functor.map_comp, Category.assoc, image.fac,
      comp_isotypicIdempotent f τ hτ χ φ hφ]
  have : IsSplitEpi M := ⟨⟨inv ((f)^*[ModuleCat.{u + 1} Λ].map φ ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _)) ≫
      (f)^*[ModuleCat.{u + 1} Λ].map (φ ≫ factorThruImage (isotypicIdempotent f τ hτ χ)),
    by rw [Category.assoc, hfac, IsIso.inv_hom_id]⟩⟩
  have : IsIso M := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
    rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
      ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
    set s' := Y.algClosurePoint s
    have : Mono ((Scheme.pointSmallEtale s').sheafFiber.map M) := by
      rw [hM, sheafFiber_map_upperStar_map_comp_counit]
      have := mono_sheafFiber_map_image_ι_isotypicIdempotent_comp_stalkRestrict f τ hτ χ hadd
        (s' ≫ f) ⟨s', rfl⟩ fun t ↦ htrans _ s' t.1 (by rw [t.2])
      infer_instance
    exact isIso_of_mono_of_isSplitEpi _
  have : (f)^*[ModuleCat.{u + 1} Λ].map (φ ≫ factorThruImage (isotypicIdempotent f τ hτ χ)) =
      ((f)^*[ModuleCat.{u + 1} Λ].map φ ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _)) ≫ inv M := by
    rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [this]
  infer_instance

include hadd in
/-- **Sheaves trivialized by a surjective `f` with the same descent datum are isomorphic.** If
`f` is surjective and `G` acts transitively on its geometric fibres, two sheaves `F₁`, `F₂`
with morphisms `φᵢ : Fᵢ ⟶ f_* Λ` on which `G` acts through `χ` and whose adjoints
`f^* Fᵢ ⟶ Λ` are isomorphisms are isomorphic: both are the `χ`-isotypic component of `f_* Λ`. -/
theorem nonempty_iso_of_isotypic (hf : Function.Surjective f.base)
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s t : Spec (.of Ω) ⟶ Y),
      s ≫ f = t ≫ f → ∃ g, s = t ≫ τ g)
    {F₁ F₂ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ₁ : F₁ ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _)) (φ₂ : F₂ ⟶ (f)_*[ModuleCat Λ].obj (𝟙_ _))
    (hφ₁ : ∀ g, φ₁ ≫ lowerStarConstantSheafEndOfOver f (τ g) (hτ g) = χ g • φ₁)
    (hφ₂ : ∀ g, φ₂ ≫ lowerStarConstantSheafEndOfOver f (τ g) (hτ g) = χ g • φ₂)
    (hiso₁ : IsIso ((f)^*[ModuleCat.{u + 1} Λ].map φ₁ ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _)))
    (hiso₂ : IsIso ((f)^*[ModuleCat.{u + 1} Λ].map φ₂ ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app (𝟙_ _))) :
    Nonempty (F₁ ≅ F₂) := by
  have := Etale.reflectsIsomorphisms_upperStar_of_surjective Λ f hf
  have := isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent f τ hτ χ hadd htrans φ₁
    hφ₁ hiso₁
  have := isIso_upperStar_map_comp_factorThruImage_isotypicIdempotent f τ hτ χ hadd htrans φ₂
    hφ₂ hiso₂
  have := isIso_of_reflects_iso (φ₁ ≫ factorThruImage (isotypicIdempotent f τ hτ χ))
    (f)^*[ModuleCat.{u + 1} Λ]
  have := isIso_of_reflects_iso (φ₂ ≫ factorThruImage (isotypicIdempotent f τ hτ χ))
    (f)^*[ModuleCat.{u + 1} Λ]
  exact ⟨asIso (φ₁ ≫ factorThruImage (isotypicIdempotent f τ hτ χ)) ≪≫
    (asIso (φ₂ ≫ factorThruImage (isotypicIdempotent f τ hτ χ))).symm⟩

end Finite

end AlgebraicGeometry.Etale

end
