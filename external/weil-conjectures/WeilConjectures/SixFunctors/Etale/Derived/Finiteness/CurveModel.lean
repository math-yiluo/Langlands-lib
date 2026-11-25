/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison
public import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Direct images on the pieces of a generic curve model

Two formal inputs of the proof of `proposition-proper-direct-image-finite-coefficients`:

- a surjective closed immersion `t : T ⟶ P` does not change direct images: the unit
  `F ⟶ t_* t^* F` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_unit_app_of_isClosedImmersion_of_surjective`), so that
  `Rf_*(F[0]) ≅ R(t ≫ f)_*((t^* F)[0])`;
- on a finite disjoint union `∐ₐ Yₐ`, a sheaf is the direct sum of the pushforwards of its
  restrictions to the `Yₐ` (`AlgebraicGeometry.Etale.isIso_biproductLift_unit_sigmaι`), so the
  direct image along `h : ∐ₐ Yₐ ⟶ S` has constructible homology as soon as those along the
  `Sigma.ι Y a ≫ h` have
  (`AlgebraicGeometry.Etale.constructibleHomology_rightDerivedLowerStar_sigma`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- For a surjective closed immersion `t`, the unit `F ⟶ t_* t^* F` is an isomorphism: its
pullback along `t` is one, and `t` is surjective. -/
lemma isIso_unit_app_of_isClosedImmersion_of_surjective {T P : Scheme.{u}} (t : T ⟶ P)
    [IsClosedImmersion t] [Surjective t] (F : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app F) :=
  Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun _ : PUnit.{u + 1} ↦ t) (fun x ↦ ⟨⟨⟩, t.surjective x⟩) _ fun _ ↦ inferInstance

/-- **Direct images and surjective closed immersions.** For a surjective closed immersion
`t : T ⟶ P` and `f : P ⟶ S`, `Rf_*(F[0]) ≅ R(t ≫ f)_*((t^* F)[0])`. -/
noncomputable def rightDerivedLowerStarSingleIsoOfSurjective {T P S : Scheme.{u}} (t : T ⟶ P)
    [IsClosedImmersion t] [Surjective t] (f : P ⟶ S)
    (F : Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F) ≅
      (R((t ≫ f)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((t)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  have := isIso_unit_app_of_isClosedImmersion_of_surjective t F
  (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso
      (asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app F))) ≪≫
    rightDerivedLowerStarSingleLowerStarIso t f _

section Sigma

variable {ι : Type u} (Y : ι → Scheme.{u})

/-- The range of the inclusion of a summand of a finite coproduct of schemes is closed: it is the
complement of the union of the other (open) summands. -/
lemma isClosed_range_sigmaι [Finite ι] (a : ι) : IsClosed (Set.range (Sigma.ι Y a)) := by
  classical
  have h : Set.range (Sigma.ι Y a) = (⋃ b ∈ ({a}ᶜ : Set ι), Set.range (Sigma.ι Y b))ᶜ := by
    ext x
    rw [Set.mem_compl_iff, Set.mem_iUnion₂]
    constructor
    · rintro ⟨z, rfl⟩ ⟨b, hb, w, hw⟩
      exact hb (congrArg Sigma.fst ((sigmaι_eq_iff Y b a w z).1 hw))
    · intro h
      obtain ⟨⟨c, y⟩, rfl⟩ := (sigmaMk Y).surjective x
      rw [sigmaMk_mk] at h ⊢
      by_cases hc : c = a
      · subst hc
        exact ⟨y, rfl⟩
      · exact absurd ⟨c, hc, y, rfl⟩ h
  rw [h]
  exact (isOpen_biUnion fun b _ ↦ (Sigma.ι Y b).isOpenEmbedding.isOpen_range).isClosed_compl

instance isClosedImmersion_sigmaι [Finite ι] (a : ι) : IsClosedImmersion (Sigma.ι Y a) :=
  IsClosedImmersion.of_isOpenImmersion _ (isClosed_range_sigmaι Y a)

/-- A geometric point of `∐ Y` factoring through the summand `b` has exactly one geometric point
of `Y b` over it. -/
noncomputable abbrev uniqueGeometricFiberSigmaι {Ω : Type u} [Field Ω] (b : ι)
    (s : Spec (.of Ω) ⟶ Y b) : Unique (Scheme.Hom.GeometricFiber (Sigma.ι Y b) (s ≫ Sigma.ι Y b))
    where
  default := ⟨s, rfl⟩
  uniq t := Subtype.ext ((cancel_mono (Sigma.ι Y b)).1 t.2)

/-- On a finite disjoint union `∐ₐ Yₐ`, the units `F ⟶ (ιₐ)_* ιₐ^* F` exhibit `F` as the direct
sum of the pushforwards of its restrictions to the summands. -/
lemma isIso_biproductLift_unit_sigmaι [Finite ι]
    (F : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (biproduct.lift fun a ↦
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F) := by
  classical
  set φ := biproduct.lift fun a ↦
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F
  refine isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
  obtain ⟨⟨b, y⟩, rfl⟩ := (sigmaMk Y).surjective x
  obtain ⟨s, hs⟩ := IsImmersion.exists_comp_eq_of_field (Sigma.ι Y b)
    ((∐ Y).algClosurePoint (sigmaMk Y ⟨b, y⟩)) (by simp)
  let P := (pointSmallEtale ((∐ Y).algClosurePoint (sigmaMk Y ⟨b, y⟩))).sheafFiber
    (A := ModuleCat.{u + 1} Λ)
  have : P.Additive := (pointSmallEtale _).sheafFiber_additive
  -- the stalks of the summands `a ≠ b` vanish, the stalk of the unit at `b` is invertible
  have hz (a : ι) (hab : a ≠ b) : IsZero (P.obj ((Sigma.ι Y a)_*[ModuleCat.{u + 1} Λ].obj
      ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F))) := by
    have h0 := (Etale.isZero_upperStar_lowerStar_of_disjoint_range (ModuleCat.{u + 1} Λ)
      (Sigma.ι Y b) (Sigma.ι Y a)
        (Set.disjoint_left.2 fun x ⟨w, hw⟩ ⟨z, hz⟩ ↦
          hab (congrArg Sigma.fst ((sigmaι_eq_iff Y a b z w).1 (hz.trans hw.symm))))
      ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F))
    simp only [P]
    rw [← hs]
    exact ((pointSmallEtale s).sheafFiber.map_isZero h0).of_iso
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (Sigma.ι Y b) s).app _).symm
  have hb : IsIso (P.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y b)).unit.app F)) := by
    have := uniqueGeometricFiberSigmaι Y b s
    have := isIso_sheafFiber_map_unit_of_unique (Sigma.ι Y b) (s ≫ Sigma.ι Y b) F
    simp only [P]
    rw [← hs]
    exact this
  -- a map into a direct sum all of whose other summands vanish
  have hφ : IsIso (biproduct.lift fun a ↦ P.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F)) := by
    refine ⟨biproduct.π _ b ≫ inv (P.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y b)).unit.app F)), ?_, ?_⟩
    · rw [biproduct.lift_π_assoc, IsIso.hom_inv_id]
    · refine biproduct.hom_ext _ _ fun a ↦ ?_
      by_cases hab : a = b
      · subst hab
        simp
      · exact (hz a hab).eq_of_tgt _ _
  have hcomp : P.map φ ≫ (P.mapBiproduct _).hom = biproduct.lift fun a ↦ P.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F) := by
    refine biproduct.hom_ext _ _ fun a ↦ ?_
    simp only [φ, Category.assoc, Functor.mapBiproduct_hom]
    erw [biproduct.lift_π, biproduct.lift_π, ← P.map_comp, biproduct.lift_π]
  have : IsIso (P.map φ) := by
    have : IsIso (P.map φ ≫ (P.mapBiproduct _).hom) := by
      rw [hcomp]
      exact hφ
    exact IsIso.of_isIso_comp_right _ (P.mapBiproduct _).hom
  have : IsIso (((pointSmallEtale ((∐ Y).algClosurePoint (sigmaMk Y ⟨b, y⟩))).ulift.{u + 1}
      ).sheafFiber.map φ) := by
    rw [← NatIso.naturality_2 ((pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)) φ]
    infer_instance
  exact this

/-- **Direct images of a finite direct sum.** If `Rf_*(Gⱼ[0])` has constructible homology
sheaves for each member of a finite family `(Gⱼ)` of sheaves on `X`, so has `Rf_*((⨁ⱼ Gⱼ)[0])`:
each `Hᵠ(Rf_*(-[0]))` is an additive functor, hence commutes with finite direct sums. -/
lemma constructibleHomology_rightDerivedLowerStar_biproduct {X S : Scheme.{u}} (f : X ⟶ S)
    {J : Type*} [Finite J] (G : J → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∀ j, Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj (G j)))) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj (⨁ G))) := by
  intro q
  let Φ := singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ homologyFunctor _ q
  have (j : J) : IsConstructibleSheaf ((Φ.obj ∘ G) j) := hG j q
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have (j : Fin n) : IsConstructibleSheaf ((Φ.obj ∘ G ∘ e.symm) j) := hG (e.symm j) q
  have : IsConstructibleSheaf (⨁ (Φ.obj ∘ G ∘ e.symm)) := IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (⨁ (Φ.obj ∘ G)) :=
    IsConstructibleSheaf.of_iso (F := ⨁ (Φ.obj ∘ G ∘ e.symm))
      (biproduct.whiskerEquiv (f := Φ.obj ∘ G ∘ e.symm) (g := Φ.obj ∘ G) e.symm
        fun _ ↦ Iso.refl _)
  exact IsConstructibleSheaf.of_iso (Φ.mapBiproduct G).symm

/-- **Direct images from a finite disjoint union.** For `h : ∐ₐ Yₐ ⟶ S` and a sheaf `F` on
`∐ₐ Yₐ`, if every `R(ιₐ ≫ h)_*((ιₐ^* F)[0])` has constructible homology, so has
`Rh_*(F[0])`. -/
lemma constructibleHomology_rightDerivedLowerStar_sigma [Finite ι] {S : Scheme.{u}}
    (h : ∐ Y ⟶ S) (F : Sheaf (∐ Y).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ a, Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((Sigma.ι Y a ≫ h)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((Sigma.ι Y a)^*[ModuleCat.{u + 1} Λ].obj F)))) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((h)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F)) := by
  have := isIso_biproductLift_unit_sigmaι Y F
  refine (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
    ((R((h)_*[ModuleCat.{u + 1} Λ])).mapIso ((singleFunctor _ 0).mapIso
      (asIso (biproduct.lift fun a ↦
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (Sigma.ι Y a)).unit.app F)))).symm
    (constructibleHomology_rightDerivedLowerStar_biproduct h _ fun a ↦ ?_)
  exact (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).prop_of_iso
    (rightDerivedLowerStarSingleLowerStarIso (Sigma.ι Y a) h _).symm (hF a)

end Sigma

end Etale

end AlgebraicGeometry
