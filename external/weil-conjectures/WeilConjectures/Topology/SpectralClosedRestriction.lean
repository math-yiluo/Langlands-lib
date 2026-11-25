/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Topology.SpectralClosedRestrictionSurjective

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Sheaves, Tag 008H; Etale Cohomology, Tag 09ZG,
first paragraph. Stalk comparison used in the injectivity step of Tag 09ZG.

Proof: the stalk of the inverse-image sheaf at `z` is canonically isomorphic to
`F`'s stalk at its image. The comparison is the presheaf inverse-image stalk
isomorphism followed by the stalk map of the sheafification unit; both maps are
isomorphisms. Compatibility of this comparison with germs identifies the germ
of the image of each global section with the image of its original germ. Apply
the germ map to the assumed equality of restricted sections, and cancel the
comparison isomorphism. This argument holds for every subset, including the
empty subset (where the assertion has no points); no closedness or spectrality
is needed. -/
private theorem restriction_eq_implies_germ_eq
    (X : TopCat.{u}) (Z : Set X) (F : X.Sheaf (Type u))
    (s t : F.1.obj (op ⊤))
    (h : (((Sheaf.pullbackPushforwardAdjunction (Type u)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)).unit.app F).1.app
        (op ⊤)) s =
      (((Sheaf.pullbackPushforwardAdjunction (Type u)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Z ⟶ X)).unit.app F).1.app
        (op ⊤)) t) (z : Z) :
    Presheaf.germ F.1 ⊤ z.1 (by trivial) s = Presheaf.germ F.1 ⊤ z.1 (by trivial) t := by
  let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P := (Presheaf.pullback (Type u) i).obj F.1
  let η := (Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F.1
  let θ := toSheafify (Opens.grothendieckTopology (TopCat.of Z)) P
  let R := (Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F
  let a := (Sheaf.pullbackIso (Type u) i).hom.app F
  have hc : R.1 ≫ ((Sheaf.pushforward (Type u) i).map a).1 =
      η ≫ (Presheaf.pushforward (Type u) i).map θ := by
    have : (Opens.map i).IsContinuous (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (TopCat.of Z)) := by
      apply Functor.isContinuous_of_coverPreserving
      · exact compatiblePreserving_opens_map i
      · exact coverPreserving_opens_map i
    have e := Adjunction.unit_leftAdjointUniq_hom_app
      (Sheaf.pullbackPushforwardAdjunction (Type u) i)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map i) (Type u) (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (TopCat.of Z))) F
    change R.1 ≫ ((Sheaf.pushforward (Type u) i).map a).1 = _
    exact congrArg (fun f => f.1) e
  have he : (η.app (op ⊤) ≫ θ.app (op ((Opens.map i).obj ⊤))) s =
      (η.app (op ⊤) ≫ θ.app (op ((Opens.map i).obj ⊤))) t := by
    have e := congrArg (fun f => f.app (op ⊤)) hc
    have hs := congrArg (((Sheaf.pushforward (Type u) i).map a).1.app (op ⊤)) h
    change (R.1 ≫ ((Sheaf.pushforward (Type u) i).map a).1).app (op ⊤) s =
      (R.1 ≫ ((Sheaf.pushforward (Type u) i).map a).1).app (op ⊤) t at hs
    rw [e] at hs
    exact hs
  have hθ := Presheaf.stalkFunctor_map_unit_toSheafify_isIso z (Type u) P
  have hinj := (CategoryTheory.isIso_iff_bijective
    ((Presheaf.stalkFunctor (Type u) z).map θ)).mp hθ
  have he' := congrArg
    (Presheaf.germ (sheafify (Opens.grothendieckTopology (TopCat.of Z)) P)
      ((Opens.map i).obj ⊤) z (by trivial)) he
  have hg : Presheaf.germ P ((Opens.map i).obj ⊤) z (by trivial) (η.app (op ⊤) s) =
      Presheaf.germ P ((Opens.map i).obj ⊤) z (by trivial) (η.app (op ⊤) t) := by
    apply hinj.1
    rw [Presheaf.stalkFunctor_map_germ_apply, Presheaf.stalkFunctor_map_germ_apply]
    simp only [ConcreteCategory.comp_apply] at he'
    convert he' using 1
  apply (CategoryTheory.isIso_iff_bijective
    (Presheaf.stalkPullbackIso (Type u) i F.1 z).hom).mp (inferInstance :
      IsIso (Presheaf.stalkPullbackIso (Type u) i F.1 z).hom) |>.1
  change (Presheaf.germ F.1 ⊤ (i z) (by trivial) ≫
      Presheaf.stalkPullbackHom (Type u) i F.1 z) s =
    (Presheaf.germ F.1 ⊤ (i z) (by trivial) ≫
      Presheaf.stalkPullbackHom (Type u) i F.1 z) t
  rw [Presheaf.germ_stalkPullbackHom]
  simp only [P, η] at hg
  simp only [ConcreteCategory.comp_apply]
  convert hg using 1


/-- Source: Stacks Project, Etale Cohomology, Lemma 59.82.1 (Tag 09ZG).
(blueprint: lem-weil-pbc-h0-spectral-closed-restriction)
 Proof (Stacks 09ZG): (1) restriction commutes with sheaf morphisms and is identified
 on stalks with the inverse-image stalk bijection. Every point of X specializes to Z,
 so equality on Z gives equality on all stalks and injectivity. (2) For a finite constant
 sheaf, restriction of locally constant maps is bijective by induction on the number of
 values, using the connectedness hypothesis and the clopen decomposition lift (0CAM).
 (3) The same holds for finite products of pushed-forward finite constant sheaves, by
 finite-product compatibility and the closed-subspace spectrality lemma. (4) A subsheaf
 injecting sectionwise into such a product has surjective restriction: lift locally on
 stalks, then glue using sectionwise injectivity. (5) Express an arbitrary sheaf as a
 filtered colimit of these subsheaves; restriction and sections commute with the colimit
 on the spectral closed subspace, yielding surjectivity. Together with (1), the map is
 bijective. These steps use the proof dependencies recorded in the blueprint node.
-/
theorem spectral_closed_restriction
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (F : X.Sheaf (Type u)) :
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let R := (Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app F
    Function.Bijective
      (fun s : F.1.obj (op ⊤) =>
        (R.1.app (op ⊤)) s) := by
  constructor
  · intro s t h
    apply Presheaf.section_ext F ⊤ s t
    intro x hx
    have : ConnectedSpace (↥(Z ∩ closure ({x} : Set X))) := hconn x
    obtain ⟨z⟩ := (inferInstance : Nonempty (↥(Z ∩ closure ({x} : Set X))))
    have hg := restriction_eq_implies_germ_eq X Z F s t h ⟨z.1, z.2.1⟩
    obtain ⟨W, hzW, i₁, i₂, heq⟩ := Presheaf.germ_eq F.1 z.1 (by trivial) (by trivial) s t hg
    have hxW : x ∈ W :=
      (specializes_iff_mem_closure.mpr z.2.2).mem_open W.isOpen hzW
    have hi : i₁ = i₂ := Subsingleton.elim _ _
    rw [← hi] at heq
    simpa only [Presheaf.germ_res_apply] using congrArg (Presheaf.germ F.1 W x hxW) heq
  · exact spectral_closed_restriction_surjective X Z hZ hconn F

end TopCat
