/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# The counit of `f^* ⊣ f_*` for a finite morphism

For a finite morphism `f : X ⟶ Y` the counit `f^* f_* G ⟶ G` is an epimorphism
(`AlgebraicGeometry.Etale.epi_upperStarLowerStarAdjunction_counit_app_of_isFinite`): at a
geometric point `s` of `X` with algebraically closed residue field its stalk is the projection
`(f_* G)_{f(s)} = ∏_{t ∈ X_{f(s)}} G_t ⟶ G_s` of the stalk formula
`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`. Consequently `f_*` reflects zero objects
(`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_of_isFinite`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

omit [HasSmallSiteSheafify A] in
/-- For a finite morphism `f` and a geometric point `s` of `X` with algebraically closed residue
field, the stalk at `s` of the counit `f^* f_* G ⟶ G` is an epimorphism: up to isomorphism it is
a projection out of the product of the stalk formula. -/
lemma Etale.epi_sheafFiber_map_counit_app_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (G : Sheaf X.smallEtaleTopology A) :
    Epi ((pointSmallEtale s).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)) := by
  have hr : Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G =
      (Etale.stalkIsoPi A f (s ≫ f) G).hom ≫ Pi.π _ ⟨s, rfl⟩ := by
    rw [Etale.stalkIsoPi_hom, Pi.lift_comp_π]
  have : Epi (Etale.stalkRestrict A f (s ≫ f) ⟨s, rfl⟩ G) := by
    rw [hr]
    infer_instance
  rw [Etale.stalkRestrict_eq_counit] at this
  exact epi_of_epi ((Etale.upperStarCompSheafFiberIso A f s).inv.app ((f)_*[A].obj G)) _

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The counit of `f^* ⊣ f_*` is an epimorphism for a finite morphism `f`**, as checked at
the geometric points `X.algClosurePoint x` of `X`, which jointly reflect epimorphisms. -/
instance Etale.epi_upperStarLowerStarAdjunction_counit_app_of_isFinite
    (G : Sheaf X.smallEtaleTopology A) :
    Epi ((Etale.upperStarLowerStarAdjunction A f).counit.app G) := by
  refine (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X A).epi_of_epi_map _ ?_
  rintro ⟨-, ⟨x⟩⟩
  have : Epi (((pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber.map
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)) := by
    rw [← NatIso.naturality_2 ((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso A)
      ((Etale.upperStarLowerStarAdjunction A f).counit.app G)]
    have := Etale.epi_sheafFiber_map_counit_app_of_isFinite A f (X.algClosurePoint x) G
    exact epi_comp _ _
  exact this

omit [HasSmallSiteSheafify A] in
include hJ in
/-- **The direct image along a finite morphism reflects zero objects**: if `f_* G` is zero, so
is `f^* f_* G`, which maps epimorphically onto `G`. -/
lemma Etale.isZero_of_isZero_lowerStar_of_isFinite {G : Sheaf X.smallEtaleTopology A}
    (hG : IsZero ((f)_*[A].obj G)) : IsZero G := by
  have h₀ : IsZero ((f)^*[A].obj ((f)_*[A].obj G)) := ((f)^*[A]).map_isZero hG
  rw [IsZero.iff_id_eq_zero, ← cancel_epi ((Etale.upperStarLowerStarAdjunction A f).counit.app G)]
  exact h₀.eq_of_src _ _

end AlgebraicGeometry

end
