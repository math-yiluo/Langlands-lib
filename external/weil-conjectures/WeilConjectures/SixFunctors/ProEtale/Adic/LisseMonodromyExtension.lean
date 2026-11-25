/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback

/-!
# Lisse sheaves whose monodromy factors through a quotient extend

Let `f : Y' ⟶ Y` be a morphism of connected schemes with compatible monodromies of lisse
`ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.LisseMonodromy.IsCompatible`), which are
equivalences at a base point `t` of `Y'` and at its image, and assume that
`π₁(Y', t) → π₁(Y, t ≫ f)` is surjective, as for a dense open of a normal scheme. A lisse sheaf
`G'` on `Y'` whose monodromy representation is trivial on the kernel of
`π₁(Y', t) → π₁(Y, t ≫ f)` is the pullback of a lisse sheaf on `Y`
(`AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_rep_eq_self`): its
representation factors through a continuous representation of `π₁(Y, t ≫ f)`, which is the
monodromy representation of a lisse sheaf `G` on `Y`, and `f^* G ≅ G'` since both have the same
`π₁(Y', t)`-representation.

For an open `U` of a smooth curve and the open `V = U ∪ {z}` obtained by adding a boundary point,
the kernel is the local inertia at `z`, and this says that a lisse sheaf with trivial local
monodromy at `z` extends over `z` (blueprint `corollary-unramified-boundary-point--2`).

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathHom`: the homomorphism
  `π₁(Y', y) → π₁(Y, y ≫ f)` of automorphism groups of fibre functors, which is continuous
  (`AlgebraicGeometry.Scheme.FiniteEtale.continuous_pullbackPathHom`).

## Main statements

- `AlgebraicGeometry.ProEtale.LisseMonodromy.exists_upperStar_iso_of_rep_eq_self`.
- `AlgebraicGeometry.Scheme.FiniteEtale.exists_pullbackPathHom_apply_eq`: if `P ×_Y Y'` is
  connected, `π₁(Y', y)` acts transitively on the fibre of `P` at `y ≫ f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.FiniteEtale

variable {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The homomorphism `π₁(Y', y) → π₁(Y, y ≫ f)` of automorphism groups of fibre functors induced
by a morphism `f : Y' ⟶ Y` (`AlgebraicGeometry.Scheme.FiniteEtale.pullbackPathIso`). -/
noncomputable def pullbackPathHom (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y') :
    Aut (fiber y) →* Aut (fiber (y ≫ f)) where
  toFun σ := Aut.of (pullbackPathIso f σ.asIso)
  map_one' := Aut.ext (pullbackPathIso_refl f y)
  map_mul' σ τ := Aut.ext (pullbackPathIso_trans f τ.asIso σ.asIso)

lemma pullbackPathHom_apply (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y') (σ : Aut (fiber y)) :
    pullbackPathHom f y σ = Aut.of (pullbackPathIso f σ.asIso) :=
  rfl

open PreGaloisCategory in
/-- The homomorphism `π₁(Y', y) → π₁(Y, y ≫ f)` is continuous: its component at a finite étale
`Y`-scheme `P` is determined by the component of the source at `P ×_Y Y'`. -/
lemma continuous_pullbackPathHom (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y') :
    Continuous (pullbackPathHom f y) := by
  rw [(autEmbedding_isClosedEmbedding (fiber (y ≫ f))).isInducing.continuous_iff]
  refine continuous_pi fun P ↦ ?_
  have hc : Continuous fun σ : Aut (fiber y) ↦ autEmbedding (fiber y) σ ((pullback f).obj P) :=
    (continuous_apply ((pullback f).obj P)).comp
      (autEmbedding_isClosedEmbedding (fiber y)).continuous
  exact ((continuous_of_discreteTopology (β := Aut ((fiber (y ≫ f)).obj P))
    (f := fun a : Aut ((fiber y).obj ((pullback f).obj P)) ↦
      Aut.of (((pullbackFiberIso f y).app P).symm ≪≫ a.asIso ≪≫
        (pullbackFiberIso f y).app P))).comp hc).congr
    fun σ ↦ rfl

open PreGaloisCategory in
/-- If the base change `P ×_Y Y'` of a finite étale `Y`-scheme along `f : Y' ⟶ Y` is connected,
the
automorphisms of the fibre functor at `y` act transitively on the fibre of `P` at `y ≫ f`, through
`pullbackPathHom`. -/
lemma exists_pullbackPathHom_apply_eq [ConnectedSpace Y'] (f : Y' ⟶ Y) (y : Spec (.of Ω) ⟶ Y')
    (P : Y.FiniteEtale) [IsConnected ((pullback f).obj P)] (a b : (fiber (y ≫ f)).obj P) :
    ∃ τ : Aut (fiber y), (pullbackPathHom f y τ).asIso.hom.app P a = b := by
  have key (a' : (fiber y).obj ((pullback f).obj P)) :
      ∃ τ : Aut (fiber y), τ.asIso.hom.app _ a' = (pullbackFiberIso f y).inv.app P b :=
    MulAction.exists_smul_eq _ a' _
  obtain ⟨τ, hτ⟩ := key ((pullbackFiberIso f y).inv.app P a)
  refine ⟨τ, ?_⟩
  have h : (pullbackPathHom f y τ).asIso.hom.app P a = (pullbackFiberIso f y).hom.app P
      (τ.asIso.hom.app _ ((pullbackFiberIso f y).inv.app P a)) := rfl
  rw [h, hτ]
  exact ConcreteCategory.congr_hom ((pullbackFiberIso f y).inv_hom_id_app P) b

end Scheme.FiniteEtale

namespace ProEtale

section Universal

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω] [IsLocallyNoetherian Y]
  [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y]

/-- The monodromy of lisse `ℓ`-adic sheaves on a connected regular Noetherian scheme given by its
universal profinite étale covers (`AlgebraicGeometry.Scheme.universalCovers`), on which lisse
sheaves are constant (`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`). Being a definite
choice, it is compatible with the monodromy of the same kind on any connected regular Noetherian
scheme mapping to `Y` (`AlgebraicGeometry.ProEtale.isCompatible_universalLisseMonodromy`). -/
noncomputable def universalLisseMonodromy : LisseMonodromy l Y Ω :=
  (Scheme.universalCovers Y Ω).lisseMonodromy fun y G ↦
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover _ y G.property

/-- The monodromy from universal covers is an equivalence at every base point
(`proposition-lattices-representations-normal-scheme`). -/
theorem universalLisseMonodromy_isEquivalenceAt (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) :
    (universalLisseMonodromy l Y Ω).IsEquivalenceAt t :=
  (Scheme.universalCovers Y Ω).lisseMonodromy_isEquivalenceAt _ t

variable {Y} in
/-- The monodromies from universal covers are compatible with every morphism of connected regular
Noetherian schemes. -/
theorem isCompatible_universalLisseMonodromy {Y' : Scheme.{u}} [IsLocallyNoetherian Y']
    [CompactSpace Y'] [IsRegular Y'] [ConnectedSpace Y'] (f : Y' ⟶ Y) :
    LisseMonodromy.IsCompatible f (universalLisseMonodromy l Y Ω)
      (universalLisseMonodromy l Y' Ω) :=
  fun _ _ τ G ↦ (Scheme.universalCoversHom f).lisseMonodromy_mono_upperStar _ _ τ G

end Universal

namespace LisseMonodromy

open Scheme.FiniteEtale

variable {l : ℕ} [Fact l.Prime] {Y Y' : Scheme.{u}} {Ω : Type u} [Field Ω] {f : Y' ⟶ Y}
  {M : LisseMonodromy l Y Ω} {M' : LisseMonodromy l Y' Ω}

/-- **Lisse sheaves with monodromy trivial on the kernel extend.** Let `M`, `M'` be monodromies
on `Y`, `Y'` compatible with `f : Y' ⟶ Y`, which are equivalences at `t ≫ f` and `t`, and assume
that `π₁(Y', t) → π₁(Y, t ≫ f)` is surjective. If the monodromy representation of a lisse sheaf
`G'` on `Y'` is trivial on the kernel of `π₁(Y', t) → π₁(Y, t ≫ f)`, then `G'` is the pullback
of a lisse sheaf on `Y`: the representation of `π₁(Y', t)` factors through a representation of
`π₁(Y, t ≫ f)`, continuous since `π₁(Y', t) → π₁(Y, t ≫ f)` is a quotient map of compact
Hausdorff groups, which is the monodromy representation of a lisse `G` on `Y`; then `f^* G` and
`G'` have the same representation of `π₁(Y', t)`, hence are isomorphic. -/
theorem exists_upperStar_iso_of_rep_eq_self {t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y'}
    (hM : M.IsEquivalenceAt (t ≫ f)) (hM' : M'.IsEquivalenceAt t) (hc : IsCompatible f M M')
    (hsurj : Function.Surjective (pullbackPathHom f t)) {G' : LisseSheaf l Y'}
    (hG' : ∀ σ ∈ (pullbackPathHom f t).ker, ∀ v, M'.rep t G' σ v = v) :
    ∃ G : LisseSheaf l Y, Nonempty (G.upperStar l f ≅ G') := by
  set φ := pullbackPathHom f t
  set ρ' := M'.rep t G'
  have hker : φ.ker ≤ ρ'.asGroupHom.ker := fun σ hσ ↦ by
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    rw [Representation.asGroupHom_apply]
    exact LinearMap.ext (hG' σ hσ)
  let ρu : Aut (fiber (t ≫ f)) →* (Module.End (PadicAlgCl l) (StalkSpace t G'))ˣ :=
    φ.liftOfSurjective hsurj ⟨ρ'.asGroupHom, hker⟩
  let ρ : Representation (PadicAlgCl l) (Aut (fiber (t ≫ f))) (StalkSpace t G') :=
    (Units.coeHom _).comp ρu
  have hρ (σ : Aut (fiber t)) (v : StalkSpace t G') : ρ (φ σ) v = ρ' σ v := by
    have h : ρu (φ σ) = ρ'.asGroupHom σ :=
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ'.asGroupHom, hker⟩ σ
    change ((ρu (φ σ) : Module.End (PadicAlgCl l) (StalkSpace t G'))) v = _
    rw [h, Representation.asGroupHom_apply]
  -- the representation of `π₁(Y, t ≫ f)` is continuous
  have hq : Topology.IsQuotientMap φ :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj (continuous_pullbackPathHom f t)
  have hcont (ψ : Module.Dual (PadicAlgCl l) (StalkSpace t G')) (v : StalkSpace t G') :
      Continuous fun σ ↦ ψ (ρ σ v) := by
    rw [hq.continuous_iff]
    have h : ((fun σ ↦ ψ (ρ σ v)) ∘ φ) = fun σ ↦ ψ (ρ' σ v) := funext fun σ ↦ by
      simp only [Function.comp_apply, hρ]
    rw [h]
    exact hM'.continuous_rep G' ψ v
  obtain ⟨G, e, he⟩ := hM.essSurj (StalkSpace t G') ρ hcont
  -- `f^* G` and `G'` have the same representation of `π₁(Y', t)`
  let ψ : StalkSpace t (G.upperStar l f) ≃ₗ[PadicAlgCl l] StalkSpace t G' :=
    (upperStarStalkLinearEquiv f t G).symm.trans e
  have hψ (σ : Aut (fiber t)) (w : StalkSpace t (G.upperStar l f)) :
      ψ (M'.rep t (G.upperStar l f) σ w) = ρ' σ (ψ w) := by
    obtain ⟨v, rfl⟩ := (upperStarStalkLinearEquiv f t G).surjective w
    rw [← hc.rep_apply]
    simp only [ψ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [he, ← hρ]
    rfl
  obtain ⟨g, hg⟩ := hM'.full ψ.toLinearMap fun σ w ↦ hψ σ w
  have := hM'.isIso_of_bijective g (by rw [hg]; exact ψ.bijective)
  exact ⟨G, ⟨asIso g⟩⟩

end LisseMonodromy

end ProEtale

end AlgebraicGeometry
