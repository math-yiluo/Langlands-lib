/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion

/-!
# Sheaves supported on a closed subscheme, for arbitrary coefficients

Let `j : U ⟶ X` be an open immersion and `i : Z ⟶ X` a closed immersion whose range is the
complement of the range of `j`. This file shows, for sheaves on the small étale site of `X`
with values in an arbitrary Grothendieck abelian category `A`, that a sheaf `K` with
`j^* K = 0` is of the form `i_* G`, and deduces that `j^*` and `i^*` jointly reflect
isomorphisms. The results of `WeilConjectures.SixFunctors.OpenClosed.Conservative` are the same
statements proved with stalks, for a concrete `A`.

## The argument

Base change `i.Etale : X.Etale ⥤ Z.Etale` along `i` is cover-dense, locally full and locally
faithful (`WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion`). By the comparison
lemma `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`, the pushforward along it is therefore
an equivalence between the sheaves on `Z` and the sheaves on `X` for the topology induced by
`i.Etale`, in which a sieve `S` on `W` covers when its base change covers `W ×_X Z`. A sieve
`S` covering for this topology, together with the étale `X`-schemes landing in `U`, covers `W`
in the étale topology. So an étale sheaf `K` vanishing on everything over `U` — which is what
`j^* K = 0` says — is a sheaf for the induced topology, hence the pushforward of a sheaf on `Z`.

No stalks enter, which is why the coefficient category is arbitrary.

## Main results

- `AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`: a sheaf `K` with
  `j^* K = 0` is in the essential image of `i_*`.
- `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar'`: `j^*` and `i^*` jointly
  reflect isomorphisms, for arbitrary Grothendieck abelian coefficients
  (blueprint: `prop:openclosed-conservative`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

open Scheme

section Sieve

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]

/-- The sieve on an étale `X`-scheme `W` of the étale `X`-schemes over `W` whose structure
morphism lands in the range of the open immersion `j`. -/
def sieveOfRangeSubset (W : X.Etale) : Sieve W where
  arrows V _ := Set.range V.hom.base ⊆ Set.range j.base
  downward_closed {V V'} f hf g := by
    rintro _ ⟨x, rfl⟩
    rw [← MorphismProperty.Over.w g]
    exact hf ⟨_, rfl⟩

/-- Let `i` be a morphism whose range is the complement of the range of `j`. If the base change
along `i` of a sieve `S` on `W` is an étale covering of `W ×_X Z`, then `S` together with the
étale `X`-schemes over `W` landing in `U` is an étale covering of `W`: the points of `W` over
`U` are covered by `W ×_X U`, and those over `Z` by `S`. -/
lemma sup_sieveOfRangeSubset_mem (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {W : X.Etale} (S : Sieve W)
    (hS : S.functorPushforward i.Etale ∈ Z.smallEtaleTopology (i.Etale.obj W)) :
    S ⊔ sieveOfRangeSubset j W ∈ X.smallEtaleTopology W := by
  rw [mem_smallEtaleTopology_iff]
  intro w
  by_cases hw : W.hom.base w ∈ Set.range j.base
  · -- `w` lies over `U`: it is in the preimage of `U`
    let O : W.left.Opens := W.hom ⁻¹ᵁ j.opensRange
    let g : Scheme.Etale.mk (O.ι ≫ W.hom) ⟶ W := MorphismProperty.Over.homMk O.ι rfl
    refine ⟨_, g, Or.inr ?_, ⟨⟨w, hw⟩, rfl⟩⟩
    rintro _ ⟨x, rfl⟩
    exact x.2
  · -- `w` lies over `Z`: it is the image of a point `z` of `W ×_X Z`, covered by `S`
    obtain ⟨z₀, hz₀⟩ : W.hom.base w ∈ Set.range i.base := by rw [hij]; exact hw
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom) (g := i) w z₀
      hz₀.symm
    rw [mem_smallEtaleTopology_iff] at hS
    obtain ⟨V', g', ⟨V, f, h, hf, rfl⟩, v, hv⟩ := hS z
    refine ⟨V, f, Or.inl hf, ⟨pullback.fst V.hom i (h.left v), ?_⟩⟩
    rw [← hz, ← hv]
    have key : (h.left ≫ (i.Etale.map f).left) ≫ pullback.fst W.hom i =
        (h.left ≫ pullback.fst V.hom i) ≫ f.left := by
      rw [Category.assoc, Scheme.Hom.etale_map_left_comp_fst, Category.assoc]
    exact (congrArg (fun φ ↦ φ.base v) key).symm

end Sieve

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {U Z X : Scheme.{u}} {j : U ⟶ X} (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- An étale sheaf `K` on `X` whose sections over every étale `X`-scheme landing in `U` vanish
is a sheaf for the topology on `X.Etale` induced by base change along `i`. A covering sieve `S`
for that topology becomes an étale covering after adding the étale `X`-schemes landing in `U`
(`AlgebraicGeometry.Etale.sup_sieveOfRangeSubset_mem`), and on these `K` vanishes, so the sheaf
condition for this larger sieve gives the one for `S`. -/
lemma isSheaf_inducedTopology_of_isZero (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : Sheaf X.smallEtaleTopology A)
    (hK : ∀ V : X.Etale, Set.range V.hom.base ⊆ Set.range j.base → IsZero (K.obj.obj (op V))) :
    Presheaf.IsSheaf (i.Etale.inducedTopology Z.smallEtaleTopology) K.obj := by
  intro E W S hS
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hS
  have hR := sup_sieveOfRangeSubset_mem j i hij S hS
  refine Presieve.isSheafFor_trans _ (S ⊔ sieveOfRangeSubset j W) S (K.property E _ hR)
    (fun V f _ ↦ (K.property E _ (X.smallEtaleTopology.pullback_stable f hR)).isSeparatedFor)
    (fun V f hf ↦ ?_)
  rcases hf with hf | hf
  · rw [Sieve.pullback_eq_top_of_mem S hf]
    exact Presieve.isSheafFor_top _
  · -- `V` lands in `U`, so all sections of `K` over `X`-schemes over `V` vanish
    have hz (V' : X.Etale) (g : V' ⟶ V) : IsZero (K.obj.obj (op V')) :=
      hK V' ((sieveOfRangeSubset j W).downward_closed hf g)
    intro x _
    exact ⟨(hz V (𝟙 _)).from_ E, fun V' g _ ↦ (hz V' g).eq_of_tgt _ _,
      fun y _ ↦ (hz V (𝟙 _)).eq_of_tgt _ _⟩

omit [IsClosedImmersion i] in
variable {A} in
/-- A sheaf on `X` whose restriction along the open immersion `j` vanishes has vanishing sections
over every étale `X`-scheme `V` landing in the range of `j`: such a `V` is the image of an étale
`U`-scheme under `j`, over which the sections of `K` are those of `j^* K`. -/
lemma isZero_obj_of_isZero_upperStar {K : Sheaf X.smallEtaleTopology A}
    (hK : IsZero ((j)^*[A].obj K)) (V : X.Etale) (hV : Set.range V.hom.base ⊆ Set.range j.base) :
    IsZero (K.obj.obj (op V)) := by
  let l := IsOpenImmersion.lift j V.hom hV
  have : Etale (l ≫ j) := by rw [IsOpenImmersion.lift_fac]; infer_instance
  have : Etale l := Etale.of_comp l j
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).obj
      (Scheme.Etale.mk l) ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simp [l])
  have h₀ : IsZero ((Etale.openImmersionRestriction A j).obj K) :=
    hK.of_iso ((Etale.upperStarIsoOpenImmersionRestriction A j).app K).symm
  exact (((sheafToPresheaf _ _).map_isZero h₀).obj (op (Scheme.Etale.mk l))).of_iso
    (K.obj.mapIso e.op)

variable {A} in
/-- **Sheaves supported on `Z` are pushforwards**: a sheaf `K` on `X` whose restriction to the
open complement `U` of `Z` vanishes is isomorphic to `i_* G` for a sheaf `G` on `Z`.

The sheaf `K` is a sheaf for the topology induced by base change along `i`
(`AlgebraicGeometry.Etale.isSheaf_inducedTopology_of_isZero`), and for that topology the
pushforward along `i.Etale` is an equivalence by the comparison lemma, `i.Etale` being
cover-dense, locally full and locally faithful. -/
theorem mem_essImage_lowerStar_of_isZero_upperStar
    (hij : Set.range i.base = (Set.range j.base)ᶜ) {K : Sheaf X.smallEtaleTopology A}
    (hK : IsZero ((j)^*[A].obj K)) : (i)_*[A].essImage K := by
  let F := i.Etale.sheafPushforwardContinuous A (i.Etale.inducedTopology Z.smallEtaleTopology)
    Z.smallEtaleTopology
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  have : F.IsEquivalence := inferInstanceAs (i.Etale.sheafPushforwardContinuous A
    (i.Etale.inducedTopology Z.smallEtaleTopology) Z.smallEtaleTopology).IsEquivalence
  let K' : Sheaf (i.Etale.inducedTopology Z.smallEtaleTopology) A :=
    ⟨K.obj, isSheaf_inducedTopology_of_isZero A i hij K (isZero_obj_of_isZero_upperStar hK)⟩
  -- `i_* G` and `K` have the same underlying presheaf as `F.obj G` and `K'`
  exact ⟨F.objPreimage K', ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((sheafToPresheaf (i.Etale.inducedTopology Z.smallEtaleTopology) A).mapIso
      (F.objObjPreimageIso K'))⟩⟩

variable {A} in
/-- A sheaf on `X` whose restrictions to `U` and to `Z` both vanish is zero: it is `i_* G` by
`AlgebraicGeometry.Etale.mem_essImage_lowerStar_of_isZero_upperStar`, and
`G ≅ i^* i_* G` vanishes. -/
theorem isZero_of_isZero_upperStar (hij : Set.range i.base = (Set.range j.base)ᶜ)
    {K : Sheaf X.smallEtaleTopology A} (hj : IsZero ((j)^*[A].obj K))
    (hi : IsZero ((i)^*[A].obj K)) : IsZero K := by
  obtain ⟨G, ⟨e⟩⟩ := mem_essImage_lowerStar_of_isZero_upperStar i hij hj
  have hG : IsZero G := hi.of_iso ((asIso ((Etale.upperStarLowerStarAdjunction A i).counit.app
    G)).symm ≪≫ (i)^*[A].mapIso e)
  exact ((i)_*[A].map_isZero hG).of_iso e.symm

/-- **Open–closed conservativity, for arbitrary coefficients**: the restrictions `j^*` and `i^*`
along an open immersion `j` and a closed immersion `i` with complementary ranges jointly
reflect isomorphisms of sheaves with values in any Grothendieck abelian category. Both are
exact, so the kernel and the cokernel of a morphism inverted by `j^*` and `i^*` have vanishing
restrictions to `U` and to `Z`, and vanish by
`AlgebraicGeometry.Etale.isZero_of_isZero_upperStar`.

This is `AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar` without the
concreteness assumptions on `A` that its proof through stalks needs.
(blueprint: `prop:openclosed-conservative`) -/
theorem jointlyReflectIsomorphisms_upperStar' (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor ((j)^*[A]) ((i)^*[A])) := by
  refine jointlyReflectIsomorphisms_pairFunctor _ _ fun {F G} φ hj hi ↦ ?_
  have hker {Y : Scheme.{u}} (f : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A)
      [PreservesFiniteLimits f] [IsIso (f.map φ)] : IsZero (f.obj (kernel φ)) :=
    (isZero_kernel_of_mono (f.map φ)).of_iso (PreservesKernel.iso f φ)
  have hcoker {Y : Scheme.{u}} (f : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A)
      [PreservesFiniteColimits f] [IsIso (f.map φ)] : IsZero (f.obj (cokernel φ)) :=
    (isZero_cokernel_of_epi (f.map φ)).of_iso (PreservesCokernel.iso f φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_upperStar i hij (hker (j)^*[A]) (hker (i)^*[A]))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar i hij (hcoker (j)^*[A]) (hcoker (i)^*[A]))
  exact isIso_of_mono_of_epi φ

end Etale

end AlgebraicGeometry
