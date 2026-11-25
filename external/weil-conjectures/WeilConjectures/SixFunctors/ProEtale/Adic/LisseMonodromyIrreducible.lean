/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.ContinuousIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback

/-!
# Irreducible local systems and irreducible monodromy representations

Let `M` be a monodromy of lisse `ℓ`-adic sheaves on a locally Noetherian scheme `Y` which is an
equivalence at a base point `t` (`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`).
A lisse sheaf `G` is an irreducible local system if and only if its monodromy representation
`M.rep t G` of `π₁(Y, t)` is irreducible
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt.isIrreducibleAdicLocalSystem_iff`):
invariant subspaces of the stalk are the stalks of lisse subsheaves, a morphism of lisse sheaves is
a monomorphism if and only if its stalk at `t` is injective (kernels of morphisms of lisse sheaves
being lisse on a locally Noetherian scheme), and a lisse sheaf vanishes if and only if its stalk
does.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The `ℚ̄_ℓ`-linear map of stalks at a geometric point induced by a morphism of lisse
sheaves. -/
noncomputable abbrev lisseStalkMap (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    {G H : LisseSheaf l Y} (f : G ⟶ H) :
    LisseMonodromy.StalkSpace t G →ₗ[PadicAlgCl l] LisseMonodromy.StalkSpace t H :=
  ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map f)).hom

variable (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)

lemma lisseStalkMap_comp {G H K : LisseSheaf l Y} (f : G ⟶ H) (g : H ⟶ K) :
    lisseStalkMap t (f ≫ g) = lisseStalkMap t g ∘ₗ lisseStalkMap t f := by
  simp only [lisseStalkMap, Functor.map_comp, ModuleCat.hom_comp]

lemma lisseStalkMap_id (G : LisseSheaf l Y) : lisseStalkMap t (𝟙 G) = LinearMap.id := by
  simp only [lisseStalkMap, CategoryTheory.Functor.map_id, ModuleCat.hom_id]

lemma lisseStalkMap_zero (G H : LisseSheaf l Y) :
    lisseStalkMap t (ObjectProperty.homMk (0 : G.obj ⟶ H.obj)) = 0 := by
  have : (lisseStalk l t).map (ObjectProperty.homMk (0 : G.obj ⟶ H.obj)) =
      (stalkFunctor l t).map ((AdicSheaf.forget Y).map 0) := rfl
  rw [lisseStalkMap, this, Functor.map_zero, Functor.map_zero, Functor.map_zero]
  rfl

/-- The stalk map of an isomorphism of lisse sheaves is bijective. -/
lemma lisseStalkMap_bijective {G H : LisseSheaf l Y} (f : G ⟶ H) [IsIso f] :
    Function.Bijective (lisseStalkMap t f) := by
  refine Function.bijective_iff_has_inverse.2 ⟨lisseStalkMap t (inv f), fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [← LinearMap.comp_apply, ← lisseStalkMap_comp, IsIso.hom_inv_id, lisseStalkMap_id,
      LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← lisseStalkMap_comp, IsIso.inv_hom_id, lisseStalkMap_id,
      LinearMap.id_apply]

/-- The stalks of a zero lisse sheaf vanish. -/
lemma subsingleton_stalkSpace_of_isZero (G : LisseSheaf l Y) (h : IsZero G.obj) :
    Subsingleton (LisseMonodromy.StalkSpace t G) := by
  have h' : 𝟙 G = ObjectProperty.homMk 0 := ObjectProperty.hom_ext _ (h.eq_of_src _ _)
  have hv (v : LisseMonodromy.StalkSpace t G) : v = 0 := by
    simpa [lisseStalkMap_id, lisseStalkMap_zero] using
      LinearMap.congr_fun (congrArg (lisseStalkMap t) h') v
  exact ⟨fun v w ↦ (hv v).trans (hv w).symm⟩

namespace LisseMonodromy.IsEquivalenceAt

variable {t} {M : LisseMonodromy l Y Ω}

/-- A morphism of lisse sheaves is determined by its stalk at a base point at which the monodromy
is an equivalence. -/
lemma ext_of_lisseStalkMap (hM : M.IsEquivalenceAt t) {G H : LisseSheaf l Y} {f g : G ⟶ H}
    (h : lisseStalkMap t f = lisseStalkMap t g) : f = g :=
  hM.faithful f g ((WeilCoefficients.toModuleCat l).map_injective (ModuleCat.hom_ext h))

/-- A lisse sheaf whose stalk at a base point vanishes is zero, if the monodromy at that base
point is an equivalence. -/
lemma isZero_of_subsingleton (hM : M.IsEquivalenceAt t) (G : LisseSheaf l Y)
    [Subsingleton (StalkSpace t G)] : IsZero G.obj := by
  rw [IsZero.iff_id_eq_zero]
  have h : 𝟙 G = ObjectProperty.homMk 0 :=
    hM.ext_of_lisseStalkMap (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  exact congrArg (·.hom) h

/-- The monodromy representation restricted to an invariant subspace is continuous. -/
lemma continuous_toRepresentation (hM : M.IsEquivalenceAt t) {G : LisseSheaf l Y}
    (S : Subrepresentation (M.rep t G)) (φ : Module.Dual (PadicAlgCl l) S.toSubmodule)
    (v : S.toSubmodule) : Continuous fun g ↦ φ (S.toRepresentation g v) := by
  obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend φ
  have : (fun g ↦ φ (S.toRepresentation g v)) = fun g ↦ φ' (M.rep t G g v) := funext fun g ↦ by
    rw [← hφ']
    rfl
  rw [this]
  exact hM.continuous_rep G φ' v

/-- Every invariant subspace of the stalk of a lisse sheaf at a base point at which the monodromy
is an equivalence is the image of the stalk of a lisse sheaf mapping injectively to it. -/
lemma exists_hom_range_eq (hM : M.IsEquivalenceAt t) {G : LisseSheaf l Y}
    (S : Subrepresentation (M.rep t G)) :
    ∃ (G' : LisseSheaf l Y) (a : G' ⟶ G), Function.Injective (lisseStalkMap t a) ∧
      LinearMap.range (lisseStalkMap t a) = S.toSubmodule := by
  obtain ⟨G', e, he⟩ := hM.essSurj S.toSubmodule S.toRepresentation
    (hM.continuous_toRepresentation S)
  obtain ⟨a, ha⟩ := hM.full (S.toSubmodule.subtype ∘ₗ e.toLinearMap) fun g v ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he]
    rfl
  refine ⟨G', a, ?_, ?_⟩
  · rw [show lisseStalkMap t a = _ from ha]
    exact S.toSubmodule.injective_subtype.comp e.injective
  · rw [show lisseStalkMap t a = _ from ha, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top, Submodule.range_subtype]

/-- The stalk of a monomorphism of lisse sheaves at a base point at which the monodromy is an
equivalence is injective. -/
lemma injective_of_mono (hM : M.IsEquivalenceAt t) {G H : LisseSheaf l Y} (f : G ⟶ H)
    [Mono f] : Function.Injective (lisseStalkMap t f) := by
  have hK : ∀ g, ∀ v ∈ LinearMap.ker (lisseStalkMap t f),
      M.rep t G g v ∈ LinearMap.ker (lisseStalkMap t f) := fun g v hv ↦ by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [M.rep_naturality, hv, map_zero]
  obtain ⟨G', a, -, ha⟩ := hM.exists_hom_range_eq ⟨LinearMap.ker (lisseStalkMap t f), hK⟩
  have ha' : LinearMap.range (lisseStalkMap t a) = LinearMap.ker (lisseStalkMap t f) := ha
  have h0 : a ≫ f = ObjectProperty.homMk 0 := hM.ext_of_lisseStalkMap <| by
    rw [lisseStalkMap_comp, lisseStalkMap_zero]
    ext v
    have : lisseStalkMap t a v ∈ LinearMap.ker (lisseStalkMap t f) :=
      ha' ▸ LinearMap.mem_range_self _ v
    simpa using this
  have ha0 : a = ObjectProperty.homMk 0 :=
    (cancel_mono f).1 (h0.trans (ObjectProperty.hom_ext _ zero_comp.symm))
  rw [← LinearMap.ker_eq_bot, ← ha', ha0, lisseStalkMap_zero, LinearMap.range_zero]

/-- A morphism of lisse sheaves on a locally Noetherian scheme whose stalk at a base point at which
the monodromy is an equivalence is injective is a monomorphism of sheaves: its kernel is lisse,
with vanishing stalk. -/
lemma mono_of_injective (hM : M.IsEquivalenceAt t) [IsLocallyNoetherian Y]
    {G H : LisseSheaf l Y} (f : G ⟶ H) (hf : Function.Injective (lisseStalkMap t f)) :
    Mono f.hom := by
  let K : LisseSheaf l Y :=
    ⟨kernel f.hom, (IsAdicLisseSheaf.kernel_cokernel G.property H.property f.hom).1⟩
  let ι : K ⟶ G := ObjectProperty.homMk (kernel.ι f.hom)
  have hι : ι ≫ f = ObjectProperty.homMk 0 := ObjectProperty.hom_ext _ (kernel.condition f.hom)
  have h : ι = ObjectProperty.homMk 0 := hM.ext_of_lisseStalkMap <| by
    ext v
    apply hf
    have := LinearMap.congr_fun (congrArg (lisseStalkMap t) hι) v
    rw [lisseStalkMap_comp, lisseStalkMap_zero] at this
    rw [lisseStalkMap_zero, LinearMap.zero_apply, map_zero]
    simpa using this
  exact Preadditive.mono_of_kernel_zero (congrArg (·.hom) h)

/-- **Irreducible local systems and irreducible representations.** On a locally Noetherian scheme,
a lisse sheaf is an irreducible local system if and only if its monodromy representation at a base
point at which the monodromy is an equivalence is irreducible. -/
theorem isIrreducibleAdicLocalSystem_iff (hM : M.IsEquivalenceAt t) [IsLocallyNoetherian Y]
    (G : LisseSheaf l Y) :
    IsIrreducibleAdicLocalSystem G.obj ↔ (M.rep t G).IsIrreducible := by
  rw [Representation.isIrreducible_iff]
  constructor
  · rintro ⟨-, hz, hsub⟩
    refine ⟨?_, fun S hS ↦ ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      exact hz (hM.isZero_of_subsingleton G)
    · obtain ⟨G', a, hinj, hrange⟩ := hM.exists_hom_range_eq ⟨S, hS⟩
      have hrange' : LinearMap.range (lisseStalkMap t a) = S := hrange
      have := hM.mono_of_injective a hinj
      rcases hsub G'.obj a.hom this G'.property with h | h
      · left
        have := subsingleton_stalkSpace_of_isZero t G' h
        rw [← hrange', LinearMap.range_eq_bot]
        ext v
        rw [Subsingleton.elim v 0, map_zero, LinearMap.zero_apply]
      · right
        have : IsIso ((ObjectProperty.ι (adicLisseSheaf l Y)).map a) := h
        have : IsIso a := isIso_of_fully_faithful (ObjectProperty.ι _) a
        rw [← hrange', LinearMap.range_eq_top]
        exact (lisseStalkMap_bijective t a).2
  · rintro ⟨hV, hS⟩
    refine ⟨G.property, fun hz ↦ ?_, fun G' i hi hG' ↦ ?_⟩
    · have := subsingleton_stalkSpace_of_isZero t G hz
      exact false_of_nontrivial_of_subsingleton (StalkSpace t G)
    · let a : (⟨G', hG'⟩ : LisseSheaf l Y) ⟶ G := ObjectProperty.homMk i
      have : Mono a := (ObjectProperty.ι _).mono_of_mono_map hi
      have hinj := hM.injective_of_mono a
      have hR : ∀ g, ∀ v ∈ LinearMap.range (lisseStalkMap t a),
          M.rep t G g v ∈ LinearMap.range (lisseStalkMap t a) := by
        rintro g _ ⟨w, rfl⟩
        exact ⟨M.rep t _ g w, M.rep_naturality t a g w⟩
      rcases hS _ hR with h | h
      · left
        have hv (v : StalkSpace t ⟨G', hG'⟩) : v = 0 := hinj <| by
          rw [map_zero]
          exact (Submodule.mem_bot _).1 (h ▸ LinearMap.mem_range_self _ v)
        have : Subsingleton (StalkSpace t ⟨G', hG'⟩) := ⟨fun v w ↦ (hv v).trans (hv w).symm⟩
        exact hM.isZero_of_subsingleton ⟨G', hG'⟩
      · right
        have : IsIso a := hM.isIso_of_bijective a ⟨hinj, LinearMap.range_eq_top.1 h⟩
        exact Functor.map_isIso (ObjectProperty.ι (adicLisseSheaf l Y)) a

end LisseMonodromy.IsEquivalenceAt

end AlgebraicGeometry.ProEtale
