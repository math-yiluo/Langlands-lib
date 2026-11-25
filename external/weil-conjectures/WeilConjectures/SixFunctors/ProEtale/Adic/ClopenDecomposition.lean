/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk

/-!
# `ℓ`-adic sheaves on a finite disjoint union

Let `s k : Z k ⟶ X`, for `k` in a finite type `κ`, be closed immersions whose ranges are pairwise
disjoint and cover `X`. Then the restrictions `F ↦ ((s k)^* F)_k` form an equivalence between
`ℓ`-adic sheaves on `X` and families of `ℓ`-adic sheaves on the `Z k`: the functor
`AlgebraicGeometry.ProEtale.adicUpperStarPi` is fully faithful
(`AlgebraicGeometry.ProEtale.adicUpperStarPiFullyFaithful`) and essentially surjective
(`AlgebraicGeometry.ProEtale.adicUpperStarPi_essSurj`). Both rest on the decomposition
`F ≅ ⨁ₖ (s k)_* (s k)^* F`
(`AlgebraicGeometry.ProEtale.isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Abelian.hasFiniteBiproducts

variable (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} {κ : Type} [Finite κ] {Z : κ → Scheme.{u}}
  (s : ∀ k, Z k ⟶ X) [∀ k, IsClosedImmersion (s k)]

/-- The restrictions `F ↦ ((s k)^* F)_k` to a family of schemes over `X`. -/
abbrev adicUpperStarPi : AdicSheaf l X ⥤ ∀ k, AdicSheaf l (Z k) :=
  Functor.pi' fun k ↦ (s k)^*ᵃ[l]

variable (hs : Pairwise fun k k' ↦ Disjoint (Set.range (s k).base) (Set.range (s k').base))
  (hcov : ∀ x, ∃ k, x ∈ Set.range (s k).base)

include hs hcov in
/-- A sheaf on `X` is the direct sum of the pushforwards of its restrictions to the `Z k`. -/
lemma isIso_biproductLift_unit_of_cover (F : AdicSheaf l X) :
    IsIso (biproduct.lift fun k ↦ (adicUpperStarLowerStarAdjunction l (s k)).unit.app F) := by
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  refine isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit (⊥ : X.Opens).ι s hs
    (fun k ↦ ?_) (fun x ↦ Or.inr (hcov x)) F (isZero_adicSheaf_of_isEmpty l _)
  rw [Scheme.Opens.range_ι]
  exact Set.disjoint_empty _

include hs hcov in
/-- The decomposition `F ≅ ⨁ₖ (s k)_* (s k)^* F`. -/
def biproductUnitIso (F : AdicSheaf l X) :
    F ≅ ⨁ fun k ↦ (s k)_*ᵃ[l].obj ((s k)^*ᵃ[l].obj F) :=
  @asIso _ _ _ _ (biproduct.lift fun k ↦ (adicUpperStarLowerStarAdjunction l (s k)).unit.app F)
    (isIso_biproductLift_unit_of_cover l s hs hcov F)

lemma biproductUnitIso_hom_π (F : AdicSheaf l X) (k : κ) :
    (biproductUnitIso l s hs hcov F).hom ≫ biproduct.π _ k =
      (adicUpperStarLowerStarAdjunction l (s k)).unit.app F := by
  simp [biproductUnitIso]

include hs hcov in
/-- Morphisms of sheaves on `X` are determined by their restrictions to the `Z k`. -/
lemma hom_ext_of_cover {F G : AdicSheaf l X} {φ ψ : F ⟶ G}
    (h : ∀ k, (s k)^*ᵃ[l].map φ = (s k)^*ᵃ[l].map ψ) : φ = ψ := by
  rw [← cancel_mono (biproductUnitIso l s hs hcov G).hom]
  refine biproduct.hom_ext _ _ fun k ↦ ?_
  simp only [Category.assoc, biproductUnitIso_hom_π]
  rw [← (adicUpperStarLowerStarAdjunction l (s k)).unit_naturality,
    ← (adicUpperStarLowerStarAdjunction l (s k)).unit_naturality, h k]

include hs hcov in
/-- The morphism of sheaves on `X` with prescribed restrictions to the `Z k`. -/
def homOfCover {F G : AdicSheaf l X} (g : ∀ k, (s k)^*ᵃ[l].obj F ⟶ (s k)^*ᵃ[l].obj G) :
    F ⟶ G :=
  (biproductUnitIso l s hs hcov F).hom ≫ biproduct.map (fun k ↦ (s k)_*ᵃ[l].map (g k)) ≫
    (biproductUnitIso l s hs hcov G).inv

lemma homOfCover_comp_unit {F G : AdicSheaf l X}
    (g : ∀ k, (s k)^*ᵃ[l].obj F ⟶ (s k)^*ᵃ[l].obj G) (k : κ) :
    homOfCover l s hs hcov g ≫ (adicUpperStarLowerStarAdjunction l (s k)).unit.app G =
      (adicUpperStarLowerStarAdjunction l (s k)).unit.app F ≫ (s k)_*ᵃ[l].map (g k) := by
  rw [← biproductUnitIso_hom_π l s hs hcov, homOfCover, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, biproduct.map_π, ← Category.assoc, biproductUnitIso_hom_π l s hs hcov]

lemma upperStar_map_homOfCover {F G : AdicSheaf l X}
    (g : ∀ k, (s k)^*ᵃ[l].obj F ⟶ (s k)^*ᵃ[l].obj G) (k : κ) :
    (s k)^*ᵃ[l].map (homOfCover l s hs hcov g) = g k := by
  let adj := adicUpperStarLowerStarAdjunction l (s k)
  calc (s k)^*ᵃ[l].map (homOfCover l s hs hcov g)
      _ = (s k)^*ᵃ[l].map (homOfCover l s hs hcov g) ≫ (s k)^*ᵃ[l].map (adj.unit.app G) ≫
          adj.counit.app _ := by rw [adj.left_triangle_components, Category.comp_id]
      _ = ((s k)^*ᵃ[l].map (adj.unit.app F) ≫ (s k)^*ᵃ[l].map ((s k)_*ᵃ[l].map (g k))) ≫
          adj.counit.app _ := by
        rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
          homOfCover_comp_unit l s hs hcov g k]
      _ = g k := by
        have hn := adj.counit.naturality (g k)
        simp only [Functor.comp_map, Functor.id_map] at hn
        rw [Category.assoc, hn]
        have ht := adj.left_triangle_components F
        rw [← Category.assoc, ht]
        exact Category.id_comp _

include hs hcov in
/-- **Restrictions to a finite disjoint closed cover are fully faithful.** -/
def adicUpperStarPiFullyFaithful : (adicUpperStarPi l s).FullyFaithful where
  preimage {_ _} g := homOfCover l s hs hcov g
  map_preimage g := funext fun k ↦ upperStar_map_homOfCover l s hs hcov g k
  preimage_map _ := hom_ext_of_cover l s hs hcov fun k ↦
    upperStar_map_homOfCover l s hs hcov _ k

/-- In a finite biproduct whose summands other than the `i`-th vanish, the `i`-th projection is
an isomorphism. -/
lemma _root_.CategoryTheory.Limits.biproduct.isIso_π_of_isZero {C : Type*} [Category C]
    [Preadditive C] {J : Type} [Finite J] [HasFiniteBiproducts C] (f : J → C) (i : J)
    (h : ∀ k, k ≠ i → IsZero (f k)) : IsIso (biproduct.π f i) := by
  classical
  refine ⟨⟨biproduct.ι f i, biproduct.hom_ext' _ _ fun k ↦ ?_, biproduct.ι_π_self f i⟩⟩
  by_cases hk : k = i
  · subst hk
    rw [biproduct.ι_π_self_assoc, Category.comp_id]
  · exact (h k hk).eq_of_src _ _

include hs in
/-- The restriction to `Z i` of the sum of the pushforwards of a family `Y` is `Y i`. -/
def upperStarBiproductLowerStarIso (Y : ∀ k, AdicSheaf l (Z k)) (i : κ) :
    (s i)^*ᵃ[l].obj (⨁ fun k ↦ (s k)_*ᵃ[l].obj (Y k)) ≅ Y i :=
  have hcl (k : κ) : IsClosed (Set.range (s k).base) := (s k).isClosedEmbedding.isClosed_range
  haveI := biproduct.isIso_π_of_isZero (fun k ↦ (s i)^*ᵃ[l].obj ((s k)_*ᵃ[l].obj (Y k))) i
    fun k hk ↦ isZero_adicUpperStar_adicLowerStar_of_disjoint (s k) (hcl k) (s i) (hs hk) _
  (s i)^*ᵃ[l].mapBiproduct _ ≪≫
    asIso (biproduct.π (fun k ↦ (s i)^*ᵃ[l].obj ((s k)_*ᵃ[l].obj (Y k))) i) ≪≫
      asIso ((adicUpperStarLowerStarAdjunction l (s i)).counit.app (Y i))

include hs in
/-- **Restrictions to a finite disjoint closed cover are essentially surjective.** -/
lemma adicUpperStarPi_essSurj : (adicUpperStarPi l s).EssSurj where
  mem_essImage Y := ⟨⨁ fun k ↦ (s k)_*ᵃ[l].obj (Y k),
    ⟨Pi.isoMk fun i ↦ upperStarBiproductLowerStarIso l s hs Y i⟩⟩

end AlgebraicGeometry.ProEtale
