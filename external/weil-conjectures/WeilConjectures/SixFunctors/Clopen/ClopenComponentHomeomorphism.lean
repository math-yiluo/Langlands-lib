/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Sets.Closeds
import WeilConjectures.SixFunctors.Supporting.ProfiniteClopenPullback

/-!
# Clopen inverse images and spectral connected-component spaces

Source: agent consequence of Stacks Project, `topology.tex`, Tags 0906
(lemma-spectral-pi0), 005F (lemma-connected-component-intersection), and 08ZZ
(lemma-profinite-refine-open-covering)
(blueprint: lem-sfb-spectral-clopen-component-homeomorphism).
-/

@[expose] public section

universe u v w

namespace ConnectedComponents

/-- The saturation and quotient-topology argument of Stacks Tag 0900, together with
surjectivity of the component projection, proves clopen descent for an arbitrary space.
This packages steps 4 and 5 of `lem-sfb-component-quotient-clopen-naturality`. -/
private theorem clopen_descent_aux (Z : Type w) [TopologicalSpace Z] :
    Function.Bijective
      (fun V : TopologicalSpace.Clopens (ConnectedComponents Z) ↦
        (⟨mk ⁻¹' (V : Set (ConnectedComponents Z)),
          V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Z)) ∧
    ∀ U : TopologicalSpace.Clopens Z,
      IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) ∧
      (mk : Z → ConnectedComponents Z) ⁻¹'
        ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z) := by
  have saturation (U : TopologicalSpace.Clopens Z) :
      (mk : Z → ConnectedComponents Z) ⁻¹'
        ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z) := by
    rw [connectedComponents_preimage_image, U.isClopen.biUnion_connectedComponent_eq]
  have image_clopen (U : TopologicalSpace.Clopens Z) :
      IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) := by
    rw [← isQuotientMap_coe.isClopen_preimage, saturation]
    exact U.isClopen
  refine ⟨⟨?_, ?_⟩, fun U ↦ ⟨image_clopen U, saturation U⟩⟩
  · intro V W hVW
    apply TopologicalSpace.Clopens.ext
    exact Set.preimage_injective.mpr surjective_coe (congrArg SetLike.coe hVW)
  · intro U
    exact ⟨⟨mk '' (U : Set Z), image_clopen U⟩,
      TopologicalSpace.Clopens.ext (saturation U)⟩

/-- Clopens descend bijectively through the connected-component quotient, with inverse
given by set image. The uniquely normalized continuous component map makes this descent
natural, so bijectivity on clopens is equivalent before and after taking components.
The spaces may be empty and need not satisfy any separation or compactness condition.

Source: Stacks Project, `topology.tex`, Tag 0900 (lemma-pi0-profinite), clopen saturation
passage, with Tags 004T, 0376, and 08ZL, expanded by the agent naturality calculation.
(blueprint: lem-sfb-component-quotient-clopen-naturality)

Proof for stage 3:
1. By lem-sfb-connected-component-maximality, the connected component of x contains x,
is connected, and contains every connected set through x. Mutual containment shows that
these components partition the space. Mathlib's `ConnectedComponents` is their quotient.
2. A continuous map sends connected sets to connected sets (def-weil-connected-scheme,
applied to the inverse images of a clopen partition). Maximality therefore sends the
component of x into that of f(x). This gives the normalized map h; surjectivity of mk
makes it the unique normalized map.
3. An open subset of the target quotient has open preimage under mk. Its preimage under
h pulls back along the source mk to its preimage under f. The quotient topology proves
h continuous, and also makes each mk continuous.
4. If U is clopen and x lies in U, its intersection with the component of x is a nonempty
relatively clopen subset of that connected component. Connectedness forces the whole
component into U. Thus mk inverse image of mk image of U equals U.
5. The quotient topology, applied to this identity and its complement, makes mk image
of U clopen. Inverse image under mk preserves clopens. Surjectivity gives the other
inverse identity, so these operations are inverse bijections.
6. Membership of x in the two sides of the naturality equality means respectively
h(mk x) belongs to V and mk(f x) belongs to V. Normalization identifies these conditions.
7. Naturality expresses each clopen inverse-image map as the conjugate of the other by
the two quotient clopen bijections. Conjugation preserves and reflects bijectivity.
For an empty space there is one clopen, the empty subset, and the same arguments apply. -/
theorem clopen_descent_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    ∃ h : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y),
      (h ∘ (mk : X → ConnectedComponents X) =
        (mk : Y → ConnectedComponents Y) ∘ f) ∧
      (∀ g : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y),
        g ∘ (mk : X → ConnectedComponents X) =
          (mk : Y → ConnectedComponents Y) ∘ f → g = h) ∧
      (∀ x : X, h (mk x) = mk (f x)) ∧
      (∀ (Z : Type w) [TopologicalSpace Z],
        Function.Bijective
          (fun V : TopologicalSpace.Clopens (ConnectedComponents Z) ↦
            (⟨mk ⁻¹' (V : Set (ConnectedComponents Z)),
              V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Z)) ∧
        ∀ U : TopologicalSpace.Clopens Z,
          IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) ∧
          (mk : Z → ConnectedComponents Z) ⁻¹'
            ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z)) ∧
      (∀ V : TopologicalSpace.Clopens (ConnectedComponents Y),
        (mk : X → ConnectedComponents X) ⁻¹' (h ⁻¹' (V : Set (ConnectedComponents Y))) =
          f ⁻¹' ((mk : Y → ConnectedComponents Y) ⁻¹' (V : Set (ConnectedComponents Y)))) ∧
      (Function.Bijective
        (fun U : TopologicalSpace.Clopens Y ↦
          (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens X)) ↔
        Function.Bijective
          (fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
            (⟨h ⁻¹' (V : Set (ConnectedComponents Y)), V.isClopen.preimage h.continuous⟩ :
              TopologicalSpace.Clopens (ConnectedComponents X)))) := by
  let h : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y) :=
    ⟨hf.connectedComponentsMap, hf.connectedComponentsMap_continuous⟩
  refine ⟨h, rfl, ?_, fun _ ↦ rfl, clopen_descent_aux, fun _ ↦ rfl, ?_⟩
  · intro g hg
    apply ContinuousMap.ext
    intro c
    obtain ⟨x, rfl⟩ := surjective_coe c
    exact congrFun hg x
  · let βX := fun V : TopologicalSpace.Clopens (ConnectedComponents X) ↦
      (⟨mk ⁻¹' (V : Set (ConnectedComponents X)),
        V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens X)
    let βY := fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
      (⟨mk ⁻¹' (V : Set (ConnectedComponents Y)),
        V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Y)
    let F := fun U : TopologicalSpace.Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens X)
    let H := fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
      (⟨h ⁻¹' (V : Set (ConnectedComponents Y)),
        V.isClopen.preimage h.continuous⟩ :
          TopologicalSpace.Clopens (ConnectedComponents X))
    have hβX : Function.Bijective βX := (clopen_descent_aux X).1
    have hβY : Function.Bijective βY := (clopen_descent_aux Y).1
    have square : F ∘ βY = βX ∘ H := rfl
    change Function.Bijective F ↔ Function.Bijective H
    rw [← Function.Bijective.of_comp_iff F hβY, square]
    exact hβX.of_comp_iff' H

end ConnectedComponents

/-- A continuous map of spectral spaces whose inverse-image map on clopens is bijective
induces a homeomorphism of connected-component quotients, normalized by the quotient maps.
No nonemptiness assumption is imposed.

Source: agent consequence of Stacks Project, `topology.tex`, Tags 0906
(lemma-spectral-pi0), 005F (lemma-connected-component-intersection), and 08ZZ
(lemma-profinite-refine-open-covering)
(blueprint: lem-sfb-spectral-clopen-component-homeomorphism).

Proof for stage 3:
1. A continuous map sends each connected component into a connected component. The induced
map `h = hf.connectedComponentsMap` satisfies `h ∘ q_T = q_S ∘ f`; the quotient topology
makes it continuous, and surjectivity of `q_T` makes it the unique normalized map.
2. By `lem-pe-spectral-components-profinite`, both component quotients are compact Hausdorff
and totally disconnected. Apply `lem-weil-pbc-profinite-clopen-basis` to both quotients.
3. Every clopen of any space is a union of its connected components. Thus inverse image
under the quotient map bijects the clopens of the quotient with the clopens of the space:
the inverse sends a saturated clopen to its image, which is clopen by the quotient topology.
The normalization conjugates the given clopen-preimage bijection to that of `h`.
4. Distinct points of the source quotient can be separated by a clopen, using the clopen
basis. Express that clopen as an inverse image under `h`; its two points must have distinct
images. Hence `h` is injective.
5. If a point `y` of the target quotient is outside the image, choose around every image
point a clopen excluding `y`. Their inverse images cover the compact source quotient, so
finitely many suffice. Their finite union `V` excludes `y` but contains the image. Thus
`h` has equal inverse images of `V` and the whole target, contradicting injectivity on
clopens. This argument permits the empty finite cover when the source is empty.
6. Every clopen of the source quotient is `h`-preimage of a target clopen. Bijectivity of
`h` identifies its image with that target clopen. The clopen basis then shows `h` is open,
so its inverse is continuous. This proves the homeomorphism and the stated normalization.
If the target quotient is empty, the existence of `h` forces the source quotient empty. -/
theorem isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage
    {T : Type u} {S : Type v} [TopologicalSpace T] [TopologicalSpace S]
    [SpectralSpace T] [SpectralSpace S] {f : T → S} (hf : Continuous f)
    (hclop : Function.Bijective
      (fun U : TopologicalSpace.Clopens S ↦
        (⟨f ⁻¹' (U : Set S), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens T))) :
    IsHomeomorph hf.connectedComponentsMap ∧
      hf.connectedComponentsMap ∘ (ConnectedComponents.mk : T → ConnectedComponents T) =
        (ConnectedComponents.mk : S → ConnectedComponents S) ∘ f := by
  obtain ⟨h, hnorm, _, _, _, _, hclop_iff⟩ :=
    ConnectedComponents.clopen_descent_naturality.{u, v, u} f hf
  obtain ⟨hTcompact, hThausdorff, hTdisconnected⟩ :=
    spectralSpace_connectedComponents_profinite (T := T)
  obtain ⟨hScompact, hShausdorff, hSdisconnected⟩ :=
    spectralSpace_connectedComponents_profinite (T := S)
  have : CompactSpace (ConnectedComponents T) := hTcompact
  have : T2Space (ConnectedComponents T) := hThausdorff
  have : TotallyDisconnectedSpace (ConnectedComponents T) := hTdisconnected
  have : CompactSpace (ConnectedComponents S) := hScompact
  have : T2Space (ConnectedComponents S) := hShausdorff
  have : TotallyDisconnectedSpace (ConnectedComponents S) := hSdisconnected
  obtain ⟨hinj, hsurj, _, hopen⟩ :=
    bijective_and_isOpenMap_of_bijective_clopen_preimage h.continuous (hclop_iff.mp hclop)
  have heq : (h : ConnectedComponents T → ConnectedComponents S) =
      hf.connectedComponentsMap := by
    apply ConnectedComponents.surjective_coe.injective_comp_right
    exact hnorm
  rw [← heq]
  exact ⟨⟨h.continuous, hopen, hinj, hsurj⟩, hnorm⟩
