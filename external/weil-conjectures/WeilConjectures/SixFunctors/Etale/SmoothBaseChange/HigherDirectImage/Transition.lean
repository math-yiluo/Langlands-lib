/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOverCoherence
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineContinuity
import WeilConjectures.AlgebraicGeometry.SmallEtaleAffineColimitDetection

/-!
# Transition maps of higher direct images

For a commutative triangle `a ≫ h = h'` of schemes, with `a : Y' ⟶ Y` and `h : Y ⟶ X`, there
is a canonical map `Rh_* K ⟶ Rh'_* (a^* K)`, the composite of the unit of `Lh'^* ⊣ Rh'_*`,
the composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and the counit of `Lh^* ⊣ Rh_*`. In degree
`q` it gives the transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images. These
are the maps along which higher direct images are compared when the source scheme varies, as
in the limit theorem `AlgebraicGeometry.Etale.higherDirectImage_limit`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarPlusTransition`: the map `Rh_* K ⟶ Rh'_* (a^* K)`.
- `AlgebraicGeometry.Etale.higherDirectImageTransition`: the map
  `R^q h_* F ⟶ R^q h'_* a^* F`.

## Main statements

- `AlgebraicGeometry.Etale.higherDirectImage_limit`: higher direct images commute with limits
  of schemes along affine transition morphisms.

## References

- Stacks Project, Lemma 59.51.7, <https://stacks.math.columbia.edu/tag/09Z1>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lemma-reduction-field`: Higher direct images and limits of schemes.

Let `W ⟶ S` be a morphism of schemes, `G` a sheaf of `Λ`-modules on `W_ét`, and
`T = lim T_i` a cofiltered limit of schemes over `W` with affine transition morphisms, all
quasi-compact and quasi-separated over `S`. Then `colim_i R^q g_{i,*} (G|_{T_i}) ≅
R^q g_* (G|_T)`, where `g_i : T_i ⟶ S` and `g : T ⟶ S` are the structure morphisms. The
statement is recorded on every geometric stalk, in the form of the two defining properties of
a filtered colimit of modules: every element at the limit comes from some stage, and an element
of a stage dying at the limit already dies at a later stage. This is the case of the blueprint
statement for a system of sheaves pulled back from a fixed scheme. 
(blueprint: sbc-lem-higher-image-pulledback-stalk-continuity)
-/
@[stacks 09Z1]
theorem Etale.higherDirectImage_limit {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Over W) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)] [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)] (q : ℤ) (s : S) :
    (∀ y : ((S.uliftPointSmallEtale s).sheafFiber.obj (Etale.higherDirectImage Λ
        (c.pt.hom ≫ k) q (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) : ModuleCat.{u + 1} Λ),
      ∃ (i : I) (y' : ((S.uliftPointSmallEtale s).sheafFiber.obj
        (Etale.higherDirectImage Λ ((D.obj i).hom ≫ k) q
          (((D.obj i).hom)^*[ModuleCat.{u + 1} Λ].obj G)) : ModuleCat.{u + 1} Λ)),
        ((S.uliftPointSmallEtale s).sheafFiber.map
          (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = y) ∧
    ∀ (i : I) y', ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (c.π.app i))).hom y' = 0 →
      ∃ (j : I) (f : j ⟶ i), ((S.uliftPointSmallEtale s).sheafFiber.map
        (Etale.higherDirectImageOverMap Λ k G q (D.map f))).hom y' = 0 :=
  by
    let t := fun {U V : Over W} (φ : U ⟶ V) ↦
      Etale.higherDirectImageOverMap Λ k G q φ
    obtain ⟨hid, hcomp⟩ := Etale.higher_image_over_transition_coherence Λ k G q
    let K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      { obj := fun i ↦ Etale.higherDirectImage Λ ((D.obj i.unop).hom ≫ k) q
          ((((D.obj i.unop).hom)^*[ModuleCat.{u + 1} Λ]).obj G)
        map := fun f ↦ t (D.map f.unop)
        map_id := fun i ↦ by
          change t (D.map (𝟙 i.unop)) = 𝟙 _
          rw [D.map_id]
          exact hid _
        map_comp := fun f g ↦ by
          change t (D.map (g.unop ≫ f.unop)) = t (D.map f.unop) ≫ t (D.map g.unop)
          rw [D.map_comp]
          exact hcomp _ _ }
    let B : Cocone K :=
      { pt := Etale.higherDirectImage Λ (c.pt.hom ≫ k) q
          (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G)
        ι :=
          { app := fun i ↦ t (c.π.app i.unop)
            naturality := fun i j f ↦ by
              change t (D.map f.unop) ≫ t (c.π.app j.unop) =
                t (c.π.app i.unop) ≫ 𝟙 _
              rw [← hcomp, c.w, Category.comp_id] } }
    have hB : Nonempty (IsColimit B) :=
      Etale.nonempty_isColimit_of_affine_etale Λ S K B (fun V ↦
        Etale.nonempty_isColimit_higher_image_affine Λ k G q D c hc K
          (fun _ ↦ Iso.refl _) (fun _ ↦ by
            simp only [K, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
            rfl)
          B (Iso.refl _)
          (fun _ ↦ by
            simp only [B, t, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
            exact (Category.comp_id _).symm) V)
    let fiber := (S.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    let M := K ⋙ fiber
    let C := fiber.mapCocone B
    have hC : IsColimit C := isColimitOfPreserves fiber hB.some
    have : PreservesFilteredColimitsOfSize.{u, u}
        (forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget (ModuleCat.{u + 1} Λ))
    constructor
    · intro y
      obtain ⟨i, y', hy⟩ := Concrete.isColimit_exists_rep M hC y
      exact ⟨i.unop, y', hy⟩
    · intro i y' hy
      have hz : C.ι.app (Opposite.op i) y' = C.ι.app (Opposite.op i) 0 := by
        change (fiber.map (t (c.π.app i))).hom y' = (fiber.map (t (c.π.app i))).hom 0
        simpa only [map_zero] using hy
      obtain ⟨j, f, g, hfg⟩ :=
        Concrete.isColimit_exists_of_rep_eq M hC y' 0 hz
      refine ⟨j.unop, f.unop, ?_⟩
      change (fiber.map (t (D.map f.unop))).hom y' =
        (fiber.map (t (D.map g.unop))).hom 0 at hfg
      simpa only [map_zero] using hfg

end AlgebraicGeometry
