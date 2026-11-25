/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Closed immersions and `ℓ`-adic sheaves

The statements of `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` about
the pushforward along a closed immersion, transported to sheaves of modules over the constant
`ℓ`-adic sheaf, the forgetful functor to sheaves of `ℚ̄_ℓ`-modules reflecting isomorphisms and
zero objects; together with two vanishing statements for extensions by zero and pushforwards,
and the decomposition of a sheaf supported on finitely many closed subschemes.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl`: a
  sheaf vanishing on the open complement of a closed immersion `i` is `i_* i^*` of itself.
- `AlgebraicGeometry.ProEtale.isIso_of_forall_isIso_adicUpperStar_map`: pullbacks along a finite
  quasi-compact jointly surjective family detect isomorphisms.
- `AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek_of_isPullback`:
  the restriction of an extension by zero `j_! N` to an open `W` vanishes if `N` vanishes on the
  preimage of `W`.
- `AlgebraicGeometry.ProEtale.isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit`: a sheaf
  vanishing away from finitely many pairwise disjoint closed subschemes is the direct sum of its
  restrictions to them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

section ClosedImmersion

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The counit `i^* i_* G ⟶ G` of `ℓ`-adic sheaves along a closed immersion is invertible
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`). -/
instance isIso_adicUpperStarLowerStarAdjunction_counit :
    IsIso (adicUpperStarLowerStarAdjunction l i).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  have : IsIso ((adicUpperStarLowerStarAdjunction l i).counit.app N).hom := by
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_counit_app_hom]
    infer_instance
  have : IsIso ((AdicSheaf.forget Z).map ((adicUpperStarLowerStarAdjunction l i).counit.app N)) :=
    this
  exact isIso_of_reflects_iso _ (AdicSheaf.forget Z)

variable (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- Blueprint `lemma-passing-schematic-closure--1` for `ℓ`-adic sheaves: a sheaf `F`
vanishing on the quasi-compact open complement of a closed immersion `i` is `i_* i^* F`: the unit
`F ⟶ i_* i^* F` is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`). -/
theorem isIso_adicUpperStarLowerStarAdjunction_unit_app_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (F : AdicSheaf l X)
    (hF : IsZero ((j)^*ᵃ[l].obj F)) :
    IsIso ((adicUpperStarLowerStarAdjunction l i).unit.app F) := by
  have : IsIso ((adicUpperStarLowerStarAdjunction l i).unit.app F).hom := by
    rw [adicUpperStarLowerStarAdjunction, Adjunction.modAdjunction_unit_app_hom]
    exact isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i j hij F.X
      ((AdicSheaf.forget U).map_isZero hF)
  have : IsIso ((AdicSheaf.forget X).map ((adicUpperStarLowerStarAdjunction l i).unit.app F)) :=
    this
  exact isIso_of_reflects_iso _ (AdicSheaf.forget X)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--4` for `ℓ`-adic sheaves: the
pushforward along a closed immersion with quasi-compact open complement is exact
(`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`). -/
theorem preservesFiniteColimits_adicLowerStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesFiniteColimits (i)_*ᵃ[l] := by
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := ULift.{u + 1} (PadicAlgCl l)) i j hij
  have : PreservesFiniteColimits ((i)_*ᵃ[l] ⋙ AdicSheaf.forget X) :=
    inferInstanceAs (PreservesFiniteColimits (AdicSheaf.forget Z ⋙ (i)_*[WeilCoefficients.{u} l]))
  exact preservesFiniteColimits_of_reflects_of_preserves _ (AdicSheaf.forget X)

end ClosedImmersion

section Vanishing

variable {Z Y X : Scheme.{u}}

/-- The pullback of a pushforward `i_* G` along a morphism `g` whose range misses the closed
range of `i` vanishes: `g` factors through the open complement of the range of `i`, on which
`i_* G` vanishes. -/
lemma isZero_adicUpperStar_adicLowerStar_of_disjoint (i : Z ⟶ X) (hi : IsClosed (Set.range i.base))
    (g : Y ⟶ X) (hig : Disjoint (Set.range i.base) (Set.range g.base)) (G : AdicSheaf l Z) :
    IsZero ((g)^*ᵃ[l].obj ((i)_*ᵃ[l].obj G)) := by
  let V : X.Opens := ⟨(Set.range i.base)ᶜ, hi.isOpen_compl⟩
  have hgV : Set.range g.base ⊆ Set.range V.ι.base := by
    rw [V.range_ι]
    exact hig.subset_compl_left
  have hV : IsZero ((V.ι)^*ᵃ[l].obj ((i)_*ᵃ[l].obj G)) :=
    AdicSheaf.isZero_of_isZero_X ((isZero_openImmersionRestriction_lowerStar _ i V.ι
      (by rw [V.range_ι]; exact Set.inter_compl_self _) G.X).of_iso
        ((upperStarIsoOpenImmersionRestriction _ V.ι).app _))
  exact ((IsOpenImmersion.lift V.ι g hgV)^*ᵃ[l].map_isZero hV).of_iso
    ((adicUpperStarCongr l (IsOpenImmersion.lift_fac V.ι g hgV).symm).app _ ≪≫
      (adicUpperStarComp l _ _).app _)

/-- **Restriction of an extension by zero to an open.** For a cartesian square of open
immersions

```
  W' --j'--> W
  |          |
  w'         w
  v          v
  U  --j-->  X
```

the restriction `w^* j_! N` vanishes as soon as `w'^* N` does: the adjunctions and the base
change isomorphism `j^* w_* ≅ w'_* j'^*` turn `Hom(w^* j_! N, H)` into `Hom(w'^* N, j'^* H)`. -/
lemma isZero_adicUpperStar_adicOpenImmersionLowerShriek_of_isPullback {U W W' : Scheme.{u}}
    {j : U ⟶ X} [IsOpenImmersion j] {w : W ⟶ X} {w' : W' ⟶ U} {j' : W' ⟶ W}
    [IsOpenImmersion j'] (hsq : IsPullback w' j' j w) (N : AdicSheaf l U)
    (hN : IsZero ((w')^*ᵃ[l].obj N)) :
    IsZero ((w)^*ᵃ[l].obj ((j)_!ᵃ[l].obj N)) := by
  have := isIso_adicBaseChangeMap_of_isPullback l hsq
  refine (isZero_zero _).of_iso (IsInitial.uniqueUpToIso (IsInitial.ofUnique (h := fun H ↦ ?_))
    HasZeroObject.zeroIsInitial)
  haveI : Unique ((w')^*ᵃ[l].obj N ⟶ (j')^*ᵃ[l].obj H) :=
    ⟨⟨hN.isInitial.to _⟩, fun _ ↦ hN.isInitial.hom_ext _ _⟩
  exact Equiv.unique (((adicUpperStarLowerStarAdjunction l w).homEquiv _ H).trans
    (((adicOpenImmersionLowerShriekAdjunction l j).homEquiv N _).trans
      ((Iso.homCongr (Iso.refl N) ((asIso (adicBaseChangeMap l hsq.toCommSq)).app H)).trans
        ((adicUpperStarLowerStarAdjunction l w').homEquiv N _).symm)))

end Vanishing

section Detection

variable {X : Scheme.{u}} {κ : Type*} [Finite κ] {Z : κ → Scheme.{u}} (g : ∀ k, Z k ⟶ X)
  [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k).base)

include hg in
/-- An `ℓ`-adic sheaf whose pullbacks along a finite quasi-compact jointly surjective family
vanish is zero (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero`). -/
theorem isZero_of_forall_isZero_adicUpperStar (F : AdicSheaf l X)
    (h : ∀ k, IsZero ((g k)^*ᵃ[l].obj F)) : IsZero F := by
  refine AdicSheaf.isZero_of_isZero_X ((IsZero.iff_id_eq_zero _).2 ?_)
  refine eq_zero_of_forall_upperStar_map_eq_zero _ g hg (𝟙 F.X) fun k ↦ ?_
  rw [CategoryTheory.Functor.map_id]
  exact ((AdicSheaf.forget _).map_isZero (h k)).eq_of_src _ _

include hg in
/-- Pullbacks along a finite quasi-compact jointly surjective family detect isomorphisms of
`ℓ`-adic sheaves: they are exact and detect the vanishing of the kernel and the cokernel. -/
theorem isIso_of_forall_isIso_adicUpperStar_map {F G : AdicSheaf l X} (φ : F ⟶ G)
    (h : ∀ k, IsIso ((g k)^*ᵃ[l].map φ)) : IsIso φ := by
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (isZero_of_forall_isZero_adicUpperStar g hg _ fun k ↦
      (isZero_kernel_of_mono ((g k)^*ᵃ[l].map φ)).of_iso (PreservesKernel.iso _ φ))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_forall_isZero_adicUpperStar g hg _ fun k ↦
      (isZero_cokernel_of_epi ((g k)^*ᵃ[l].map φ)).of_iso (PreservesCokernel.iso _ φ))
  exact isIso_of_mono_of_epi φ

end Detection

section Decomposition

attribute [local instance] Abelian.hasFiniteBiproducts

variable {U X : Scheme.{u}} (j : U ⟶ X) [QuasiCompact j] {κ : Type}
  [Finite κ] {Z : κ → Scheme.{u}} (s : ∀ k, Z k ⟶ X) [∀ k, IsClosedImmersion (s k)]

/-- **A sheaf supported on finitely many disjoint closed subschemes is the sum of its
restrictions.** Let `s k : Z k ⟶ X` be finitely many closed immersions with pairwise disjoint
ranges, covering together with a quasi-compact open immersion `j` the scheme `X`. For an
`ℓ`-adic sheaf `F` vanishing on `U`, the units `F ⟶ (s k)_* (s k)^* F` induce an isomorphism
`F ≅ ⨁ₖ (s k)_* (s k)^* F`. This is checked after pullback along `j` and the `s k`
(`AlgebraicGeometry.ProEtale.isIso_of_forall_isIso_adicUpperStar_map`): along `j` both sides
vanish, and along `s k` all summands but the `k`-th vanish, while the `k`-th component is
inverse to the counit isomorphism by a triangle identity. -/
theorem isIso_biproductLift_adicUpperStarLowerStarAdjunction_unit
    (hs : Pairwise fun k k' ↦ Disjoint (Set.range (s k).base) (Set.range (s k').base))
    (hjs : ∀ k, Disjoint (Set.range (s k).base) (Set.range j.base))
    (hcov : ∀ x, x ∈ Set.range j.base ∨ ∃ k, x ∈ Set.range (s k).base)
    (F : AdicSheaf l X) (hF : IsZero ((j)^*ᵃ[l].obj F)) :
    IsIso (biproduct.lift fun k ↦ (adicUpperStarLowerStarAdjunction l (s k)).unit.app F) := by
  let T : Option κ → Scheme.{u} := fun o ↦ Option.rec (motive := fun _ ↦ Scheme.{u}) U Z o
  let g : ∀ o, T o ⟶ X := fun o ↦ Option.rec (motive := fun o ↦ T o ⟶ X) j s o
  have : ∀ o, QuasiCompact (g o) := by
    rintro (_ | k)
    · exact inferInstanceAs (QuasiCompact j)
    · exact inferInstanceAs (QuasiCompact (s k))
  have hcl (k : κ) : IsClosed (Set.range (s k).base) := (s k).isClosedEmbedding.isClosed_range
  refine isIso_of_forall_isIso_adicUpperStar_map g (fun x ↦ ?_) _ ?_
  · obtain hx | ⟨k, hx⟩ := hcov x
    · exact ⟨none, hx⟩
    · exact ⟨some k, hx⟩
  rintro (_ | k)
  · have ht : IsZero ((j)^*ᵃ[l].obj (⨁ fun k ↦ (s k)_*ᵃ[l].obj ((s k)^*ᵃ[l].obj F))) :=
      (biproduct.isZero_of_forall_isZero fun k ↦ isZero_adicUpperStar_adicLowerStar_of_disjoint
        (s k) (hcl k) j (hjs k) _).of_iso ((j)^*ᵃ[l].mapBiproduct _)
    exact ⟨⟨0, hF.eq_of_src _ _, ht.eq_of_src _ _⟩⟩
  · let Φ := (s k)^*ᵃ[l]
    let adj := adicUpperStarLowerStarAdjunction l (s k)
    have hk : IsIso (Φ.map (adj.unit.app F)) := by
      have : IsIso (Φ.map (adj.unit.app F) ≫ adj.counit.app (Φ.obj F)) := by
        rw [adj.left_triangle_components F]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
    have : IsIso (biproduct.lift fun k' ↦
        Φ.map ((adicUpperStarLowerStarAdjunction l (s k')).unit.app F)) :=
      biproduct.isIso_lift_of_isZero _ k fun k' hk' ↦
        isZero_adicUpperStar_adicLowerStar_of_disjoint (s k') (hcl k') (s k) (hs hk') _
    have h := biproduct.map_lift_mapBiprod Φ _
      (fun k' ↦ (adicUpperStarLowerStarAdjunction l (s k')).unit.app F)
    rw [← h] at this
    exact IsIso.of_isIso_comp_right (Φ.map _) ((Φ.mapBiproduct _).hom)

end Decomposition

end AlgebraicGeometry.ProEtale
