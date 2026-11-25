/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.SmallSubobject
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible

/-!
# Constructible module objects embed into pushforwards of finitely presented ones

Let `Λ` be a commutative condensed ring and `X` a scheme with noetherian underlying space. This
file shows that the constructible module objects over `Λ_X` are essentially small (blueprint
`lemma-hypotheses-brown-representability--5`).

* For finitely many quasi-compact morphisms `g k : W k ⟶ X` jointly covering `X`, the units
  `M ⟶ (g k)_* (g k)^* M` are jointly monomorphic
  (`ProEtale.CondensedRing.mono_pi_lift_unit_upperStarLowerStarAdjunction`), since the
  pullbacks `(g k)^*` jointly detect zero objects.
* A constructible `M` is pro-étale locally finitely presented on the strata of a stratification;
  refining the pro-étale covers of the (quasi-compact) strata by finitely many affine opens, `M`
  embeds into a finite product `∏ₖ (gₖ)_* hₖ^* coker(φₖ)`, for presentations
  `φₖ : Λ^{mₖ} ⟶ Λ^{nₖ}` on schemes `Uₖ` and morphisms `hₖ : Wₖ ⟶ Uₖ`, `gₖ : Wₖ ⟶ X`
  (`ProEtale.CondensedRing.exists_mono_of_isConstructibleModuleObject`).
* Such data form a set, and the module objects form a well-powered category, so the
  constructible module objects are essentially small
  (`ProEtale.CondensedRing.essentiallySmall_isConstructibleModuleObject_of_noetherianSpace`).

## Implementation note

The objects `g^* M` and `g_* N` are wrapped in the definitions `ProEtale.CondensedRing.pullObj`
and `ProEtale.CondensedRing.pushObj`. Without them, the kernel checks definitional equalities
such as `(g ≫ f)^*.obj M = (g' ≫ f')^*.obj M` (with `g = g'` and `f = f'` only up to
reduction) by unfolding the pullback functors, which times out.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A finitely presented module object `f^* N` over `f^* Λ_X`, read over `Λ_W` through the
isomorphism of ring objects `α_f : f^* Λ_X ⟶ Λ_W`, is finitely presented. -/
lemma isFinitelyPresented_upperStar_of_mapMod {W X : Scheme.{u}} (f : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Mod.IsFinitelyPresented ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N)) :
    Mod.IsFinitelyPresented (condensedRingObj Λ W) ((f)^*⟦Λ⟧.obj N) :=
  Mod.IsFinitelyPresented.of_iso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)).obj N)).symm
    (h.comap (asIso (condensedPullbackHom Λ f)).inv)

/-- **Pullbacks along a quasi-compact jointly surjective family are jointly monomorphic.** For
finitely many quasi-compact morphisms `g k : W k ⟶ X` jointly covering `X`, the units
`M ⟶ (g k)_* (g k)^* M` of a module object `M` over `Λ_X` are jointly monomorphic: the
pullbacks of their common kernel vanish, so it vanishes
(`ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`). -/
lemma mono_pi_lift_unit_upperStarLowerStarAdjunction {X : Scheme.{u}} {κ : Type} [Finite κ]
    {W : κ → Scheme.{u}} (g : ∀ k, W k ⟶ X) [∀ k, QuasiCompact (g k)]
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono (Pi.lift fun k ↦ (upperStarLowerStarAdjunction Λ (g k)).unit.app M) := by
  refine Preadditive.mono_of_isZero_kernel _ (isZero_of_isZero_X Λ ?_)
  rw [IsZero.iff_id_eq_zero]
  refine ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g hg _ fun k ↦ ?_
  let ι := kernel.ι (Pi.lift fun k ↦ (upperStarLowerStarAdjunction Λ (g k)).unit.app M)
  have hι : (g k)^*⟦Λ⟧.map ι = 0 := by
    have h0 : ι ≫ (upperStarLowerStarAdjunction Λ (g k)).unit.app M = 0 := by
      rw [← Pi.lift_comp_π (fun k ↦ (upperStarLowerStarAdjunction Λ (g k)).unit.app M) k,
        ← Category.assoc, kernel.condition, zero_comp]
    calc (g k)^*⟦Λ⟧.map ι = (g k)^*⟦Λ⟧.map ι ≫ (g k)^*⟦Λ⟧.map
          ((upperStarLowerStarAdjunction Λ (g k)).unit.app M) ≫
          (upperStarLowerStarAdjunction Λ (g k)).counit.app ((g k)^*⟦Λ⟧.obj M) := by simp
      _ = 0 := by rw [← Category.assoc, ← Functor.map_comp, h0, Functor.map_zero, zero_comp]
  have hz : IsZero ((g k)^*⟦Λ⟧.obj (kernel
      (Pi.lift fun k ↦ (upperStarLowerStarAdjunction Λ (g k)).unit.app M))) :=
    IsZero.of_mono_eq_zero _ hι
  exact (((Mod.forget _).map_isZero hz).of_iso (upperStarObjXIso Λ (g k) _).symm).eq_of_src _ _

/-! ### Presentation data -/

/-- The underlying object `g^* M` of the pullback of a module object. (A wrapper, so that
pullbacks along different but equal morphisms are compared argumentwise.) -/
noncomputable def pullObj {W X : Scheme.{u}} (g : W ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W) :=
  (g)^*⟦Λ⟧.obj M

/-- The underlying object `g_* N` of the pushforward of a module object. (A wrapper, so that
pushforwards along different but equal morphisms are compared argumentwise.) -/
noncomputable def pushObj {W X : Scheme.{u}} (g : W ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  (g)_*⟦Λ⟧.obj N

/-- The unit `M ⟶ g_* g^* M` of the adjunction `g^* ⊣ g_*`. -/
noncomputable def unitHom {W X : Scheme.{u}} (g : W ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    M ⟶ pushObj Λ g (pullObj Λ g M) :=
  (upperStarLowerStarAdjunction Λ g).unit.app M

/-- The units `M ⟶ g_* g^* M` along finitely many quasi-compact morphisms jointly covering `X`
are jointly monomorphic. -/
lemma mono_pi_lift_unitHom {X : Scheme.{u}} {κ : Type} [Finite κ]
    {W : κ → Scheme.{u}} (g : ∀ k, W k ⟶ X) [∀ k, QuasiCompact (g k)]
    (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mono (Pi.lift fun k ↦ unitHom Λ (g k) M) :=
  mono_pi_lift_unit_upperStarLowerStarAdjunction Λ g hg M

/-- The isomorphism `(h ≫ f ≫ i)^* M ≅ h^* N` induced by an isomorphism `f^* i^* M ≅ N`. -/
noncomputable def pullObjCompCompIso {W U V X : Scheme.{u}} (h : W ⟶ U) (f : U ⟶ V)
    (i : V ⟶ X) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)}
    (e : (f)^*⟦Λ⟧.obj ((i)^*⟦Λ⟧.obj M) ≅ N) :
    pullObj Λ (h ≫ f ≫ i) M ≅ pullObj Λ h N :=
  (upperStarComp Λ h (f ≫ i)).app M ≪≫ (h)^*⟦Λ⟧.mapIso ((upperStarComp Λ f i).app M ≪≫ e)

/-- The data of a finitely presented module object `coker(φ)` over `Λ_U` on a scheme `U` and
morphisms `h : W ⟶ U`, `g : W ⟶ X`: they index the module objects `g_* h^* coker(φ)`, finite
products of which every constructible module object over `Λ_X` embeds into. -/
structure PresentationDatum (X : Scheme.{u}) where
  /-- The scheme carrying the presentation. -/
  U : Scheme.{u}
  /-- The source of the restriction. -/
  W : Scheme.{u}
  /-- The restriction morphism. -/
  h : W ⟶ U
  /-- The morphism to `X`. -/
  g : W ⟶ X
  /-- The rank of the source of the presentation. -/
  m : ℕ
  /-- The rank of the target of the presentation. -/
  n : ℕ
  /-- The presentation. -/
  φ : Mod.finiteFree (condensedRingObj Λ U) m ⟶ Mod.finiteFree (condensedRingObj Λ U) n

variable {Λ} in
/-- The module object `g_* h^* coker(φ)` over `Λ_X` attached to a presentation datum. -/
noncomputable def PresentationDatum.obj {X : Scheme.{u}} :
    PresentationDatum Λ X → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  | ⟨_, _, h, g, _, _, φ⟩ => pushObj Λ g (pullObj Λ h (cokernel φ))

/-- A finite family of presentation data. -/
structure PresentationFamily (X : Scheme.{u}) where
  /-- The finite index type. -/
  ι : Type
  [finite : Finite ι]
  /-- The presentation data. -/
  datum : ι → PresentationDatum Λ X

attribute [instance] PresentationFamily.finite

variable {Λ} in
/-- The finite product `∏ₖ (gₖ)_* hₖ^* coker(φₖ)` attached to a finite family of presentation
data. -/
noncomputable def PresentationFamily.obj {X : Scheme.{u}} (F : PresentationFamily Λ X) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  ∏ᶜ fun k ↦ (F.datum k).obj

/-- A module object `M` over `Λ_X` with isomorphisms `gₖ^* M ≅ hₖ^* coker(φₖ)`, for finitely
many quasi-compact `gₖ` jointly covering `X`, embeds into `∏ₖ (gₖ)_* hₖ^* coker(φₖ)`. -/
lemma exists_mono_presentationFamily_obj {X : Scheme.{u}} {κ : Type} [Finite κ]
    {U W : κ → Scheme.{u}} (h : ∀ k, W k ⟶ U k) (g : ∀ k, W k ⟶ X) {m n : κ → ℕ}
    (φ : ∀ k, Mod.finiteFree (condensedRingObj Λ (U k)) (m k) ⟶
      Mod.finiteFree (condensedRingObj Λ (U k)) (n k))
    [∀ k, QuasiCompact (g k)] (hg : ∀ x, ∃ k, x ∈ Set.range (g k))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : ∀ k, pullObj Λ (g k) M ≅ pullObj Λ (h k) (cokernel (φ k))) :
    ∃ (F : PresentationFamily Λ X) (ψ : M ⟶ F.obj), Mono ψ := by
  have := mono_pi_lift_unitHom Λ g hg M
  let ι : (∏ᶜ fun k ↦ pushObj Λ (g k) (pullObj Λ (g k) M)) ≅
      ∏ᶜ fun k ↦ pushObj Λ (g k) (pullObj Λ (h k) (cokernel (φ k))) :=
    Pi.mapIso fun k ↦ (g k)_*⟦Λ⟧.mapIso (ε k)
  exact ⟨⟨κ, fun k ↦ ⟨U k, W k, h k, g k, m k, n k, φ k⟩⟩,
    Pi.lift (fun k ↦ unitHom Λ (g k) M) ≫ ι.hom,
    @mono_comp _ _ _ _ _ _ this _ (IsIso.mono_of_iso _)⟩

/-- Every constructible module object `M` over `Λ_X`, on a scheme `X` with noetherian
underlying space, embeds into a finite product `∏ₖ (gₖ)_* hₖ^* coker(φₖ)` of pushforwards of
pullbacks of finitely presented module objects. -/
theorem exists_mono_of_isConstructibleModuleObject {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    ∃ (F : PresentationFamily Λ X) (ψ : M ⟶ F.obj), Mono ψ := by
  obtain ⟨S, hS⟩ := hM
  choose 𝒰 h𝒰 using fun a ↦ (isLocallyFinitelyPresented_mapMod_iff Λ (S.immersion a) M).1 (hS a)
  have hcpt (a : Fin S.n) : IsCompact ((⊤ : (S.domain a).Opens) : Set (S.domain a)) := by
    rw [TopologicalSpace.Opens.coe_top, (S.immersion a).isEmbedding.isCompact_iff]
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hqc (a : Fin S.n) : QuasiCompactCover (𝒰 a).toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.1 (𝒰 a).mem₀.1
  choose m l V hV hVcov using fun a ↦
    QuasiCompactCover.exists_isAffineOpen_of_isCompact (𝒰 a).toPreZeroHypercover (hcpt a)
  choose p q φ e using fun (a : Fin S.n) (i : (𝒰 a).I₀) ↦ isFinitelyPresented_upperStar_of_mapMod
    Λ ((𝒰 a).f i) _ (h𝒰 a i)
  have : ∀ x : Σ a, Fin (m a), QuasiCompact
      ((V x.1 x.2).ι ≫ (𝒰 x.1).f (l x.1 x.2) ≫ S.immersion x.1) := fun x ↦ by
    have : IsAffine (V x.1 x.2) := hV x.1 x.2
    infer_instance
  refine exists_mono_presentationFamily_obj Λ (fun x : Σ a, Fin (m a) ↦ (V x.1 x.2).ι)
    (fun x ↦ (V x.1 x.2).ι ≫ (𝒰 x.1).f (l x.1 x.2) ≫ S.immersion x.1)
    (fun x ↦ φ x.1 (l x.1 x.2)) (fun x ↦ ?_) M fun x ↦ pullObjCompCompIso Λ (V x.1 x.2).ι
      ((𝒰 x.1).f (l x.1 x.2)) (S.immersion x.1) M (e x.1 (l x.1 x.2)).some
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
  rw [← S.range_immersion a] at ha
  obtain ⟨y, rfl⟩ := ha
  have hy : y ∈ ⋃ i, (𝒰 a).f (l a i) '' (V a i) := by
    rw [hVcov a]
    trivial
  obtain ⟨i, z, hz, rfl⟩ := by simpa using hy
  exact ⟨⟨a, i⟩, ⟨z, hz⟩, by simp⟩

/-- Blueprint `lemma-hypotheses-brown-representability--5` (constructible hearts): on a scheme with
noetherian underlying space, the constructible module objects over `Λ_X` are essentially small. They
embed into finite products of pushforwards of finitely presented module objects
(`ProEtale.CondensedRing.exists_mono_of_isConstructibleModuleObject`), which form a set, and the
category of module objects is well-powered. -/
theorem essentiallySmall_isConstructibleModuleObject_of_noetherianSpace (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstructibleModuleObject (condensedRingObj Λ X)) :=
  ObjectProperty.EssentiallySmall.of_forall_exists_mono _ PresentationFamily.obj
    fun M hM ↦ exists_mono_of_isConstructibleModuleObject Λ M hM

end AlgebraicGeometry.ProEtale.CondensedRing
