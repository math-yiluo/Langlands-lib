/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# The constant `ℓ`-adic sheaf `ℚ̄_ℓ` on the pro-étale site

Let `ℓ` be a prime and `ℚ̄_ℓ = PadicAlgCl ℓ`. The `ℓ`-adic sheaves of the blueprint are
modules over the pro-étale sheaf of *continuous* `ℓ`-adic functions, not over the constant
sheaf of the discrete ring `ℚ̄_ℓ` (Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8).
For a finite extension `E` of `ℚ_ℓ` this is the sheaf `E_X : U ↦ C(U, E)`; for `ℚ̄_ℓ`, the union
of the finite extensions, it is the sheaf `ℚ̄_ℓ,X` whose sections over a quasi-compact `U` are
`colim_E C(U, E)`: the continuous functions `U → ℚ̄_ℓ` whose values span a finite-dimensional
`ℚ_ℓ`-subspace. A finite-dimensional `ℚ_ℓ`-subspace of `ℚ̄_ℓ` carries its unique Hausdorff
vector space topology as subspace topology, so continuity may be tested in `ℚ̄_ℓ`.

Since this condition is local, `ℚ̄_ℓ,X(U)` is, for an arbitrary scheme `U`, the module
`PadicAlgCl.locallyFiniteFunctions ℓ U` of continuous functions `f : U → ℚ̄_ℓ` such that every
point has a neighbourhood on which the values of `f` span a finite-dimensional
`ℚ_ℓ`-subspace. This defines a presheaf `AlgebraicGeometry.adicFunctionsPresheaf` on all
schemes, a sheaf for the fpqc topology, and `AlgebraicGeometry.ProEtale.adicConstantSheaf ℓ X`
is its restriction to the small pro-étale site of `X`, a sheaf of modules over `ℚ̄_ℓ`
(`AlgebraicGeometry.isSheaf_fpqcTopology_adicFunctionsPresheaf`).

It is *not* the constant sheaf of the discrete module `ℚ̄_ℓ`, whose sections are the locally
constant functions: that sheaf is of étale origin, and the constructible sheaves of étale origin
with coefficients in a field of characteristic zero all vanish.

## Main definitions

- `AlgebraicGeometry.WeilCoefficients`: the coefficient category of `ℓ`-adic pro-étale sheaves,
  modules over `ℚ̄_ℓ`, lifted to the universe of the sites.
- `PadicAlgCl.locallyFiniteFunctions`: continuous functions with locally finite-dimensional
  `ℚ_ℓ`-span of values.
- `AlgebraicGeometry.adicFunctionsPresheaf`: the presheaf `U ↦ ℚ̄_ℓ,X(U)` on all schemes.
- `AlgebraicGeometry.ProEtale.adicConstantSheaf`: the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.adicConstantSheafLowerStarIso`: for an isomorphism `e : X ≅ Y`,
  `e_* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,Y`.

## Main results

- `AlgebraicGeometry.ProEtale.not_isZero_adicConstantSheaf`: `ℚ̄_ℓ,X` is nonzero on a nonempty
  scheme.
- `AlgebraicGeometry.ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange`: the action of
  an automorphism `σ` of `X` over `Y` on `g_* ℚ̄_ℓ,X` commutes with the exchange isomorphism
  `(b⁻¹)_* g_* ℚ̄_ℓ,X ≅ g_* ℚ̄_ℓ,X` of automorphisms `a`, `b` compatible with `g` and `σ`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite Topology

section LocallyFiniteFunctions

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (T : Type*) [TopologicalSpace T]

/-- The continuous functions `f : T → ℚ̄_ℓ` whose values span, locally on `T`, a
finite-dimensional `ℚ_ℓ`-subspace. For compact `T` these are the continuous functions with values
in a finite-dimensional `ℚ_ℓ`-subspace, the sections of the constant `ℓ`-adic sheaf
`ℚ̄_ℓ = colim_E E` over a quasi-compact scheme. They form a `ℚ̄_ℓ`-subalgebra: the values of a
product lie in the product of the two finite-dimensional spans. -/
noncomputable def locallyFiniteFunctions : Subalgebra (PadicAlgCl l) C(T, PadicAlgCl l) where
  carrier := {f | ∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U))}
  zero_mem' x := by
    refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, -, rfl⟩
    simp
  add_mem' {f g} hf hg x := by
    obtain ⟨U, hU, hfU⟩ := hf x
    obtain ⟨V, hV, hgV⟩ := hg x
    refine ⟨U ∩ V, Filter.inter_mem hU hV, Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℚ_[l] (f '' U) ⊔ Submodule.span ℚ_[l] (g '' V)) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨y, hy.1, rfl⟩)
      (Submodule.subset_span ⟨y, hy.2, rfl⟩)
  mul_mem' {f g} hf hg x := by
    obtain ⟨U, hU, hfU⟩ := hf x
    obtain ⟨V, hV, hgV⟩ := hg x
    have : FiniteDimensional ℚ_[l]
        ↥(Submodule.span ℚ_[l] (f '' U) * Submodule.span ℚ_[l] (g '' V)) :=
      Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hfU).mul (Module.Finite.iff_fg.1 hgV))
    refine ⟨U ∩ V, Filter.inter_mem hU hV, Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℚ_[l] (f '' U) * Submodule.span ℚ_[l] (g '' V)) ?_⟩
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨y, hy.1, rfl⟩)
      (Submodule.subset_span ⟨y, hy.2, rfl⟩)
  algebraMap_mem' c x := by
    refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℚ_[l] {c}) (Submodule.span_mono ?_)⟩
    rintro _ ⟨y, -, rfl⟩
    rfl

variable {l T}

lemma mem_locallyFiniteFunctions_iff (f : C(T, PadicAlgCl l)) :
    f ∈ locallyFiniteFunctions l T ↔
      ∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U)) :=
  Iff.rfl

/-- The constant functions are locally finite: their values span a line. -/
lemma const_mem_locallyFiniteFunctions (c : PadicAlgCl l) :
    ContinuousMap.const T c ∈ locallyFiniteFunctions l T := by
  intro x
  refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] {c}) (Submodule.span_mono ?_)⟩
  rintro _ ⟨y, -, rfl⟩
  rfl

/-- On a compact space, the values of a locally finite function span a finite-dimensional
`ℚ_ℓ`-subspace. -/
lemma finiteDimensional_span_range_of_mem_locallyFiniteFunctions [CompactSpace T]
    {f : C(T, PadicAlgCl l)} (hf : f ∈ locallyFiniteFunctions l T) :
    FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Set.range f)) := by
  choose U hU hfin using hf
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ ↦ hU x)
  refine Submodule.finiteDimensional_of_le (S₂ := t.sup fun x ↦ Submodule.span ℚ_[l] (f '' U x))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact Finset.le_sup (f := fun x ↦ Submodule.span ℚ_[l] (f '' U x)) hx
    (Submodule.subset_span ⟨y, hyx, rfl⟩)

/-- A continuous function whose values span a finite-dimensional `ℚ_ℓ`-subspace is locally
finite. -/
lemma mem_locallyFiniteFunctions_of_finiteDimensional {f : C(T, PadicAlgCl l)}
    (hf : FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (Set.range f))) :
    f ∈ locallyFiniteFunctions l T := fun _ ↦
  ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
    (Submodule.span_mono (Set.image_subset_range _ _))⟩

variable {T' : Type*} [TopologicalSpace T']

/-- Precomposition with a continuous map preserves local finiteness. -/
lemma comp_mem_locallyFiniteFunctions {f : C(T, PadicAlgCl l)}
    (hf : f ∈ locallyFiniteFunctions l T) (g : C(T', T)) :
    f.comp g ∈ locallyFiniteFunctions l T' := by
  intro x
  obtain ⟨U, hU, hfU⟩ := hf (g x)
  refine ⟨g ⁻¹' U, g.continuous.continuousAt.preimage_mem_nhds hU,
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (f '' U))
      (Submodule.span_mono ?_)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨g y, hy, rfl⟩

variable (l) in
/-- Precomposition with a continuous map `g : T' → T`, as a `ℚ̄_ℓ`-linear map of locally
finite functions. -/
noncomputable def locallyFiniteFunctionsComp (g : C(T', T)) :
    locallyFiniteFunctions l T →ₗ[PadicAlgCl l] locallyFiniteFunctions l T' where
  toFun f := ⟨f.1.comp g, comp_mem_locallyFiniteFunctions f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma locallyFiniteFunctionsComp_apply_coe (g : C(T', T)) (f : locallyFiniteFunctions l T) :
    ((locallyFiniteFunctionsComp l g f : locallyFiniteFunctions l T') :
      C(T', PadicAlgCl l)) = (f : C(T, PadicAlgCl l)).comp g :=
  rfl

end PadicAlgCl

end LocallyFiniteFunctions

namespace AlgebraicGeometry

/-- The coefficients of `ℓ`-adic pro-étale sheaves: modules over `ℚ̄_ℓ`, lifted to
`Type (u + 1)`, the universe of the `Hom`-types of sheaves on the sites of `Scheme.{u}`. The
`ℓ`-adic topology does not enter the coefficient category: it enters through the constant sheaf
`AlgebraicGeometry.ProEtale.adicConstantSheaf`. -/
abbrev WeilCoefficients (l : ℕ) [Fact l.Prime] : Type (u + 2) :=
  ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))

namespace WeilCoefficients

variable (l : ℕ) [Fact l.Prime]

/-- The underlying `ℚ̄_ℓ`-vector space of a module over `ULift ℚ̄_ℓ`, by restriction of scalars
along `ℚ̄_ℓ ≃ ULift ℚ̄_ℓ`. -/
noncomputable abbrev toModuleCat :
    WeilCoefficients.{u} l ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  ModuleCat.restrictScalars (ULift.ringEquiv (R := PadicAlgCl l)).symm.toRingHom

variable {l}

/-- An isomorphism of modules over `ULift ℚ̄_ℓ` as a `ℚ̄_ℓ`-linear isomorphism of the
underlying `ℚ̄_ℓ`-vector spaces. -/
noncomputable def linearEquivOfIso {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (toModuleCat l).obj M ≃ₗ[PadicAlgCl l] (toModuleCat l).obj N :=
  ((toModuleCat l).mapIso e).toLinearEquiv

/-- A `ℚ̄_ℓ`-linear map, lifted to a `ULift ℚ̄_ℓ`-linear map of the universe lifts. -/
noncomputable def uliftLinearMap {M N : Type*} [AddCommGroup M] [Module (PadicAlgCl l) M]
    [AddCommGroup N] [Module (PadicAlgCl l) N] (φ : M →ₗ[PadicAlgCl l] N) :
    ULift.{u + 1} M →ₗ[ULift.{u + 1} (PadicAlgCl l)] ULift.{u + 1} N where
  toFun x := ULift.up (φ x.down)
  map_add' x y := congrArg ULift.up (φ.map_add x.down y.down)
  map_smul' c x := congrArg ULift.up (φ.map_smul c.down x.down)

end WeilCoefficients

variable (l : ℕ) [Fact l.Prime]

open PadicAlgCl WeilCoefficients

/-- The presheaf `U ↦ ℚ̄_ℓ,U(U)` on all schemes: the continuous functions `U → ℚ̄_ℓ` whose
values locally span finite-dimensional `ℚ_ℓ`-subspaces, with restriction given by
precomposition with the underlying continuous maps. -/
@[simps]
noncomputable def adicFunctionsPresheaf : Scheme.{u}ᵒᵖ ⥤ WeilCoefficients.{u} l where
  obj U := ModuleCat.of _ (ULift.{u + 1} (locallyFiniteFunctions l U.unop))
  map f := ModuleCat.ofHom (uliftLinearMap (locallyFiniteFunctionsComp l f.unop.base.hom))

/-- The presheaf of continuous maps to `ULift ℚ̄_ℓ` on `Scheme.{u}`, with values in
`Type (u + 1)`. -/
noncomputable abbrev adicContinuousMapPresheaf : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  continuousMapPresheaf (ULift.{u + 1} (PadicAlgCl l))

/-- The locally finite functions, as a subfunctor of the continuous maps to `ULift ℚ̄_ℓ`. -/
noncomputable def adicFunctionsSubfunctor : Subfunctor (adicContinuousMapPresheaf.{u} l) where
  obj U := {s | (ContinuousMap.mk ULift.down continuous_uliftDown).comp s ∈
    locallyFiniteFunctions l U.unop}
  map {_ _} f _ hs := comp_mem_locallyFiniteFunctions hs f.unop.base.hom

/-- The locally finite functions form a Zariski sheaf: the condition is local. -/
lemma isSheaf_zariskiTopology_adicFunctionsSubfunctor :
    Presieve.IsSheaf Scheme.zariskiTopology (adicFunctionsSubfunctor.{u} l).toFunctor := by
  have hT := (isSheaf_iff_isSheaf_of_type _ _).1
    (isSheaf_zariskiTopology_continuousMapPresheaf (ULift.{u + 1} (PadicAlgCl l)))
  refine ((adicFunctionsSubfunctor l).isSheaf_iff hT).2 fun U s hs x ↦ ?_
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hs
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  obtain ⟨W, hW, hfin⟩ := h𝒰 _ _ (Presieve.ofArrows.mk i) y
  refine ⟨(𝒰.f i).base '' W, (𝒰.f i).isOpenEmbedding.isOpenMap.image_mem_nhds hW, ?_⟩
  rw [Set.image_image]
  exact hfin

/-- The locally finite functions satisfy the sheaf condition for a faithfully flat
`Spec S ⟶ Spec R`: the gluing of a locally finite function on the compact `Spec S` takes the
same values, which span a finite-dimensional subspace. -/
lemma isSheafFor_singleton_adicFunctionsSubfunctor {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : Flat (Spec.map f)) (hs : Surjective (Spec.map f)) :
    Presieve.IsSheafFor (adicFunctionsSubfunctor.{u} l).toFunctor (.singleton (Spec.map f)) := by
  have hT : Presieve.IsSheafFor (adicContinuousMapPresheaf.{u} l) (.singleton (Spec.map f)) := by
    have := (isSheaf_iff_isSheaf_of_type _ _).1
      (isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{u + 1} (PadicAlgCl l)))
    rw [Scheme.fpqcTopology_eq_propQCTopology] at this
    exact ((isSheaf_type_propQCTopology_iff _).1 this).2 f hf hs
  rw [Presieve.isSheafFor_singleton] at hT ⊢
  intro x hx
  obtain ⟨t, ht, ht'⟩ := hT x.1 (fun p₁ p₂ h ↦ congrArg Subtype.val (hx p₁ p₂ h))
  refine ⟨⟨t, ?_⟩, Subtype.ext ht, fun t' h' ↦ Subtype.ext (ht' _ (congrArg Subtype.val h'))⟩
  apply mem_locallyFiniteFunctions_of_finiteDimensional
  have hx' := finiteDimensional_span_range_of_mem_locallyFiniteFunctions x.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ_[l] (Set.range
    ((ContinuousMap.mk ULift.down continuous_uliftDown).comp x.1))) (Submodule.span_mono ?_)
  rintro _ ⟨y, rfl⟩
  obtain ⟨z, rfl⟩ := (Spec.map f).surjective y
  exact ⟨z, by rw [← ht]; rfl⟩

/-- The locally finite functions form an fpqc sheaf. -/
lemma isSheaf_fpqcTopology_adicFunctionsSubfunctor :
    Presieve.IsSheaf Scheme.fpqcTopology (adicFunctionsSubfunctor.{u} l).toFunctor := by
  rw [Scheme.fpqcTopology_eq_propQCTopology, isSheaf_type_propQCTopology_iff]
  exact ⟨isSheaf_zariskiTopology_adicFunctionsSubfunctor l,
    fun f hf hs ↦ isSheafFor_singleton_adicFunctionsSubfunctor l f hf hs⟩

/-- The presheaf of locally finite continuous functions is the subfunctor
`AlgebraicGeometry.adicFunctionsSubfunctor` of the continuous maps to `ULift ℚ̄_ℓ`. -/
noncomputable def adicFunctionsPresheafForgetIso :
    adicFunctionsPresheaf.{u} l ⋙ forget (WeilCoefficients.{u} l) ≅
      (adicFunctionsSubfunctor.{u} l).toFunctor :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun x := ⟨⟨fun t ↦ ULift.up (x.down.1 t), continuous_uliftUp.comp x.down.1.continuous⟩,
        x.down.2⟩
      invFun s := ULift.up ⟨(ContinuousMap.mk ULift.down continuous_uliftDown).comp s.1, s.2⟩
      left_inv _ := rfl
      right_inv _ := rfl })
    fun _ ↦ by ext x; exact Subtype.ext (ContinuousMap.ext fun _ ↦ rfl)

/-- The presheaf of locally finite continuous `ℓ`-adic functions is a sheaf for the fpqc
topology. It is a subpresheaf of the fpqc sheaf `U ↦ C(U, ℚ̄_ℓ)`
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf`) defined by a local condition,
hence a Zariski sheaf; and for a faithfully flat `Spec S ⟶ Spec R` a function on `Spec R`
whose pullback to the compact `Spec S` is locally finite has the same finite-dimensional span
of values, `Spec S ⟶ Spec R` being surjective. -/
theorem isSheaf_fpqcTopology_adicFunctionsPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (adicFunctionsPresheaf.{u} l) := by
  have : ReflectsLimitsOfSize.{u, u + 1} (forget (WeilCoefficients.{u} l)) :=
    reflectsLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  refine Presheaf.isSheaf_of_isSheaf_comp Scheme.fpqcTopology _ (forget (WeilCoefficients.{u} l))
    ((isSheaf_iff_isSheaf_of_type _ _).2 ?_)
  exact Presieve.isSheaf_iso _ (adicFunctionsPresheafForgetIso l).symm
    (isSheaf_fpqcTopology_adicFunctionsSubfunctor l)


namespace ProEtale

/-- The constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` on the small pro-étale site of `X`: the sections over a
weakly étale `U → X` are the continuous functions `U → ℚ̄_ℓ` whose values locally span
finite-dimensional `ℚ_ℓ`-subspaces (Bhatt–Scholze, §6.8). -/
noncomputable def adicConstantSheaf (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) :=
  ((Scheme.ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj
    ⟨adicFunctionsPresheaf l, .of_le Scheme.proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_adicFunctionsPresheaf l⟩

/-- The sections of `ℚ̄_ℓ,X` over `U` are the locally finite continuous functions on `U`. -/
lemma adicConstantSheaf_obj_obj (X : Scheme.{u}) (U : X.ProEt) :
    (adicConstantSheaf l X).obj.obj (op U) =
      ModuleCat.of _ (ULift.{u + 1} (locallyFiniteFunctions l U.left)) :=
  rfl

/-- Base change along an isomorphism `g : X ⟶ Y` does not change the underlying schemes of the
objects of the pro-étale site, up to the canonical isomorphisms `V ×_Y X ≅ V`. -/
noncomputable def overPullbackForgetIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g ⋙ Scheme.ProEt.forget X ⋙ Over.forget X ≅
      Scheme.ProEt.forget Y ⋙ Over.forget Y :=
  NatIso.ofComponents (fun V ↦ asIso (pullback.fst V.hom g)) fun f ↦ by
    simp

/-- The pushforward of the constant `ℓ`-adic sheaf along an isomorphism `e : X ≅ Y` is the
constant `ℓ`-adic sheaf: its sections over `V → Y` are the locally finite functions on
`V ×_Y X`, which the canonical isomorphism `V ×_Y X ≅ V` identifies with those on `V`. -/
noncomputable def adicConstantSheafLowerStarIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X) ≅ adicConstantSheaf l Y :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (show _ ≅ _ from
    (Functor.isoWhiskerRight (NatIso.op (overPullbackForgetIso e.hom))
      (adicFunctionsPresheaf l)).symm)

/-- The restriction maps of `ℚ̄_ℓ,X` are the pullbacks of functions along the underlying
morphisms of schemes. -/
lemma adicConstantSheaf_obj_map {X : Scheme.{u}} {U V : X.ProEtᵒᵖ} (f : U ⟶ V) :
    (adicConstantSheaf l X).obj.map f = (adicFunctionsPresheaf l).map f.unop.left.op :=
  rfl

lemma adicConstantSheafLowerStarIso_inv_hom_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (V : Y.ProEtᵒᵖ) :
    (adicConstantSheafLowerStarIso l e).inv.hom.app V =
      (adicFunctionsPresheaf l).map (pullback.fst V.unop.hom e.hom).op :=
  rfl

lemma adicConstantSheafLowerStarIso_hom_hom_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (V : Y.ProEtᵒᵖ) :
    (adicConstantSheafLowerStarIso l e).hom.hom.app V =
      (adicFunctionsPresheaf l).map
        (pullback.lift (𝟙 V.unop.left) (V.unop.hom ≫ e.inv) (by simp)).op := by
  rw [← cancel_mono ((adicConstantSheafLowerStarIso l e).inv.hom.app V), ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
    adicConstantSheafLowerStarIso_inv_hom_app, ← Functor.map_comp, ← op_comp,
    show pullback.fst _ _ ≫ pullback.lift _ _ _ = 𝟙 _ from
      pullback.hom_ext (by simp) (by simp [pullback.condition_assoc]), op_id,
    (adicFunctionsPresheaf l).map_id]
  rfl

/-- Let `g : X ⟶ Y` be a morphism with automorphisms `a` of `X` and `b` of `Y` such that
`g ≫ b⁻¹ = a⁻¹ ≫ g`, and let `σ` be an automorphism of `X` over `Y` commuting with `a`. Then
the action of `σ` on `g_* ℚ̄_ℓ,X`, pulling back sections along `σ` and using `σ ≫ g = g`,

`g_* ℚ̄_ℓ,X ⟶ g_* σ_* ℚ̄_ℓ,X ≅ (σ ≫ g)_* ℚ̄_ℓ,X = g_* ℚ̄_ℓ,X`,

commutes with the isomorphism

```
str : (b⁻¹)_* g_* ℚ̄_ℓ,X ≅ (g ≫ b⁻¹)_* ℚ̄_ℓ,X = (a⁻¹ ≫ g)_* ℚ̄_ℓ,X
        ≅ g_* (a⁻¹)_* ℚ̄_ℓ,X ≅ g_* ℚ̄_ℓ,X.
```

On sections over `V ⟶ Y` both composites pull functions back along `(v, x) ↦ (v, a σ x)`. -/
lemma lowerStar_map_deckAction_comp_lowerStarExchange {X Y : Scheme.{u}} (g : X ⟶ Y)
    (a : X ≅ X) (b : Y ≅ Y) (σ : X ≅ X) (hg : g ≫ b.inv = a.inv ≫ g) (hσ : σ.hom ≫ g = g)
    (hσa : σ.hom ≫ a.hom = a.hom ≫ σ.hom)
    (str : (b.inv)_*[WeilCoefficients.{u} l].obj ((g)_*[WeilCoefficients.{u} l].obj
      (adicConstantSheaf l X)) ⟶ (g)_*[WeilCoefficients.{u} l].obj (adicConstantSheaf l X))
    (hstr : str = ((lowerStarComp _ g b.inv ≪≫ lowerStarCongr _ hg ≪≫
          (lowerStarComp _ a.inv g).symm).app (adicConstantSheaf l X) ≪≫
        (g)_*[WeilCoefficients.{u} l].mapIso (adicConstantSheafLowerStarIso l a.symm)).hom) :
    (b.inv)_*[WeilCoefficients.{u} l].map
        ((g)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l σ).inv ≫
          (lowerStarComp _ σ.hom g).hom.app (adicConstantSheaf l X) ≫
          (lowerStarCongr _ hσ).hom.app (adicConstantSheaf l X)) ≫ str =
    str ≫
      ((g)_*[WeilCoefficients.{u} l].map (adicConstantSheafLowerStarIso l σ).inv ≫
          (lowerStarComp _ σ.hom g).hom.app (adicConstantSheaf l X) ≫
          (lowerStarCongr _ hσ).hom.app (adicConstantSheaf l X)) := by
  subst hstr
  ext V : 3
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app',
    Quiver.Hom.unop_op, unop_op, lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app,
    lowerStarCongr_hom_app_hom_app, adicConstantSheafLowerStarIso_inv_hom_app,
    adicConstantSheafLowerStarIso_hom_hom_app, adicConstantSheaf_obj_map]
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj,
        Iso.symm_inv, MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
        Category.comp_id, NatIso.ofComponents_inv_app, MorphismProperty.Over.isoMk_inv_left,
        pullback.congrHom_inv, MorphismProperty.Over.pullbackComp_hom_app_left,
        Category.id_comp, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, limit.lift_π,
        PullbackCone.mk_π_app, pullbackLeftPullbackSndIso_hom_fst, limit.lift_π_assoc,
        cospan_left]
      erw [pullbackLeftPullbackSndIso_inv_fst]
      simp only [pullback.lift_fst]
      exact Category.id_comp _
    · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, reassoc_of% hσa, hσ]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk, hσa]

/-- The constant `ℓ`-adic sheaf on a nonempty scheme is nonzero: the constant function `1` is a
nonzero global section. -/
theorem not_isZero_adicConstantSheaf (X : Scheme.{u}) [Nonempty X] :
    ¬ IsZero (adicConstantSheaf l X) := by
  intro h
  -- the sections over the terminal object `X` of the pro-étale site
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have h' : IsZero ((adicConstantSheaf l X).obj.obj (op T)) :=
    ((evaluation _ _).obj (op T)).map_isZero ((sheafToPresheaf _ _).map_isZero h)
  have h1 : (ULift.up ⟨ContinuousMap.const _ 1, const_mem_locallyFiniteFunctions 1⟩ :
      ULift.{u + 1} (locallyFiniteFunctions l T.left)) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 h').elim _ _
  obtain ⟨x⟩ := ‹Nonempty X›
  have := congrArg (fun f : ULift.{u + 1} (locallyFiniteFunctions l T.left) ↦
    (f.down : C(T.left, PadicAlgCl l)) x) h1
  simp at this

end ProEtale

end AlgebraicGeometry
