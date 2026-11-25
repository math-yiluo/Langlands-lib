/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafReduction
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity

/-!
# The sheaf `E_X` as `𝒪_{E,X}[1/ℓ]`

Let `E` be a subfield of `ℚ̄_ℓ` with ring of integers `𝒪_E` and `X` a scheme. The abelian sheaf
`E_X = C(-, E)` on `X_proét` (`AlgebraicGeometry.ProEtale.padicSubfieldSheaf`) is the colimit
of the tower `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`, with maps `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ E_X`
(`AlgebraicGeometry.ProEtale.isColimitPadicSubfieldSheafCocone`): that is, `E_X = 𝒪_{E,X}[1/ℓ]`.

The presheaf colimit is the presheaf of bounded functions, those `f` with `ℓⁿ f` valued in `𝒪_E`
for some `n` (`AlgebraicGeometry.ProEtale.isColimitBoundedPresheafCocone`); it is not `C(-, E)`
on non-quasi-compact objects, but every continuous function is bounded on the quasi-compact
affine opens, so its sheafification is `E_X`
(`AlgebraicGeometry.ProEtale.w_boundedToContinuousMap`).

Together with `AlgebraicGeometry.ProEtale.isColimitPadicAlgClSheafCoconeExtend` this
identifies the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X = colim_E E_X = colim_E 𝒪_{E,X}[1/ℓ]`, step (1) of
the comparison of `ℓ`-adic sheaves with `ℓ`-adic towers of torsion étale sheaves needed for the
finiteness theorem (`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The continuous functions `T → E` with bounded values: some `ℓⁿ f` takes values in `𝒪_E`. -/
noncomputable def boundedContinuousMaps (T : Type*) [TopologicalSpace T] :
    letI := normedFieldOfAlgebra l E
    AddSubgroup C(T, E) :=
  letI := normedFieldOfAlgebra l E
  { carrier := {f | ∃ n : ℕ, ∀ x, (l : E) ^ n * f x ∈ integers l E}
    add_mem' := by
      rintro f g ⟨n, hf⟩ ⟨m, hg⟩
      refine ⟨n + m, fun x ↦ ?_⟩
      have hl : (l : E) ∈ integers l E := natCast_mem (integers l E) l
      have : (l : E) ^ (n + m) * (f + g) x =
          (l : E) ^ m * ((l : E) ^ n * f x) + (l : E) ^ n * ((l : E) ^ m * g x) := by
        rw [ContinuousMap.add_apply]
        ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hl m) (hf x)) (mul_mem (pow_mem hl n) (hg x))
    zero_mem' := ⟨0, fun x ↦ by simp⟩
    neg_mem' := by
      rintro f ⟨n, hf⟩
      exact ⟨n, fun x ↦ by simpa using neg_mem (hf x)⟩ }

variable {l E} in
/-- Restriction of bounded functions along a continuous map. -/
noncomputable def boundedContinuousMapsComp {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] (g : C(T', T)) :
    letI := normedFieldOfAlgebra l E
    boundedContinuousMaps l E T →+ boundedContinuousMaps l E T' :=
  letI := normedFieldOfAlgebra l E
  { toFun f := ⟨f.1.comp g, by
      obtain ⟨n, hn⟩ := f.2
      exact ⟨n, fun x ↦ hn (g x)⟩⟩
    map_zero' := rfl
    map_add' _ _ := rfl }

/-- The bounded function `ℓ⁻ⁿ f` attached to a continuous function `f : T → 𝒪_E`. -/
noncomputable def boundedOfIntegers (n : ℕ) (T : Type*) [TopologicalSpace T] :
    letI := normedFieldOfAlgebra l E
    C(T, integers l E) →+ boundedContinuousMaps l E T :=
  letI := normedFieldOfAlgebra l E
  { toFun f := ⟨⟨fun x ↦ ((l : E) ^ n)⁻¹ * (f x : E),
        continuous_const.mul (continuous_subtype_val.comp f.continuous)⟩, n, fun x ↦ by
      rw [ContinuousMap.coe_mk, mul_inv_cancel_left₀ (pow_ne_zero n
        (natCast_ne_zero_of_algebra (l := l) (E := E)))]
      exact (f x).2⟩
    map_zero' := by
      ext x
      simp
    map_add' f g := by
      ext x
      simp [mul_add] }

lemma boundedOfIntegers_apply (n : ℕ) {T : Type*} [TopologicalSpace T]
    (f : letI := normedFieldOfAlgebra l E; C(T, integers l E)) (x : T) :
    letI := normedFieldOfAlgebra l E
    ((boundedOfIntegers l E n T f : C(T, E))) x = ((l : E) ^ n)⁻¹ * (f x : E) :=
  rfl


/-- On a compact space every continuous function to `E` is bounded. -/
lemma mem_boundedContinuousMaps_of_compactSpace {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : letI := normedFieldOfAlgebra l E; C(T, E)) :
    letI := normedFieldOfAlgebra l E
    f ∈ boundedContinuousMaps l E T := by
  let := normedFieldOfAlgebra l E
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn f.continuous.continuousOn
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (|C| + 1) by positivity)
    (inv_prime_lt_one l)
  refine ⟨n, fun x ↦ ?_⟩
  have hnorm : ‖(l : E) ^ n * f x‖ ≤ 1 := by
    have hl : ‖(l : E)‖ = (l : ℝ)⁻¹ := norm_algebraMap_natCast_self l E
    rw [norm_mul, norm_pow, hl]
    have hfx : ‖f x‖ ≤ |C| + 1 := (hC x (Set.mem_univ x)).trans ((le_abs_self C).trans (by simp))
    calc (l : ℝ)⁻¹ ^ n * ‖f x‖ ≤ (l : ℝ)⁻¹ ^ n * (|C| + 1) :=
          mul_le_mul_of_nonneg_left hfx (pow_nonneg (inv_prime_pos l).le n)
      _ ≤ 1 := by
          rw [lt_div_iff₀ (by positivity)] at hn
          exact hn.le
  exact hnorm
end PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl l)]

/-- The presheaf `U ↦ {f ∈ C(U, E) | ℓⁿ f ∈ C(U, 𝒪_E) for some n}` of bounded continuous
functions, the presheaf colimit of `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`. -/
noncomputable def boundedContinuousMapPresheaf :
    letI := normedFieldOfAlgebra l E
    X.ProEtᵒᵖ ⥤ Ab.{u + 1} :=
  letI := normedFieldOfAlgebra l E
  { obj U := AddCommGrpCat.of (ULift.{u + 1} (boundedContinuousMaps l E U.unop.left))
    map f := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((boundedContinuousMapsComp f.unop.left.base.hom).comp AddEquiv.ulift.toAddMonoidHom))
    map_id _ := rfl
    map_comp _ _ := rfl }

/-- The tower `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯` of abelian sheaves. -/
noncomputable def padicIntegersSheafMulSequence :
    letI := normedFieldOfAlgebra l E
    ℕ ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  letI := normedFieldOfAlgebra l E
  Functor.ofSequence (C := Sheaf (ProEt.topology X) Ab.{u + 1})
    (X := fun _ ↦ continuousMapAbSheaf X (integers l E))
    fun _ ↦ continuousMapAbSheafMul X (integers l E) (l : integers l E)

lemma padicIntegersSheafMulSequence_map_succ (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    (padicIntegersSheafMulSequence X l E).map (homOfLE (n.le_add_right 1)) =
      continuousMapAbSheafMul X (integers l E) (l : integers l E) :=
  letI := normedFieldOfAlgebra l E
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The maps `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ {bounded functions}`. -/
noncomputable def boundedOfIntegersPresheafHom (n : ℕ) :
    letI := normedFieldOfAlgebra l E
    (continuousMapAbSheaf X (integers l E)).obj ⟶ boundedContinuousMapPresheaf X l E :=
  letI := normedFieldOfAlgebra l E
  { app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((boundedOfIntegers l E n U.unop.left).comp AddEquiv.ulift.toAddMonoidHom))
    naturality _ _ _ := rfl }

/-- The cocone of presheaves `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ {bounded functions}` over the tower
`𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`. -/
noncomputable def boundedPresheafCocone :
    letI := normedFieldOfAlgebra l E
    Cocone (padicIntegersSheafMulSequence X l E ⋙ sheafToPresheaf _ _) :=
  letI := normedFieldOfAlgebra l E
  { pt := boundedContinuousMapPresheaf X l E
    ι := NatTrans.ofSequence (fun n ↦ boundedOfIntegersPresheafHom X l E n) fun n ↦ by
      refine Eq.trans ?_ (Category.comp_id _).symm
      rw [Functor.comp_map]
      erw [padicIntegersSheafMulSequence_map_succ]
      ext U f
      refine congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
      change ((l : E) ^ (n + 1))⁻¹ * ((l : E) * (f.down x : E)) =
        ((l : E) ^ n)⁻¹ * (f.down x : E)
      have hl := natCast_ne_zero_of_algebra (l := l) (E := E)
      field_simp
      ring }

/-- The bounded functions are the presheaf colimit of `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`:
objectwise, every bounded function is `ℓ⁻ⁿ f` for some `f` with values in `𝒪_E`, and the maps
`ℓ⁻ⁿ` are injective. -/
noncomputable def isColimitBoundedPresheafCocone :
    letI := normedFieldOfAlgebra l E
    IsColimit (boundedPresheafCocone X l E) := by
  let := normedFieldOfAlgebra l E
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine evaluationJointlyReflectsColimits _ fun U ↦ isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun s ↦ ?_) fun n a b h ↦ ⟨n, 𝟙 n, ?_⟩
  · obtain ⟨⟨f, k, hk⟩⟩ := s
    refine ⟨k, ULift.up ⟨fun x ↦ ⟨(l : E) ^ k * f x, hk x⟩,
      (continuous_const.mul f.continuous).subtype_mk _⟩, ?_⟩
    refine congrArg ULift.up (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
    change f x = ((l : E) ^ k)⁻¹ * ((l : E) ^ k * f x)
    rw [inv_mul_cancel_left₀ (pow_ne_zero k (natCast_ne_zero_of_algebra (l := l) (E := E)))]
  · obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    have hab : a = b := ContinuousMap.ext fun x ↦ Subtype.ext <| by
      have := congrArg (fun z : ULift.{u + 1} (boundedContinuousMaps l E U.unop.left) ↦
        (z.down : C(U.unop.left, E)) x) h
      exact mul_left_cancel₀
        (inv_ne_zero (pow_ne_zero n (natCast_ne_zero_of_algebra (l := l) (E := E)))) this
    subst hab
    rfl

/-- The inclusion of the bounded functions into the presheaf `U ↦ C(U, E)` underlying `E_X`. -/
noncomputable def boundedToContinuousMap :
    letI := normedFieldOfAlgebra l E
    boundedContinuousMapPresheaf X l E ⟶ (continuousMapAbSheaf X E).obj :=
  letI := normedFieldOfAlgebra l E
  { app U := AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((boundedContinuousMaps l E U.unop.left).subtype.comp AddEquiv.ulift.toAddMonoidHom))
    naturality _ _ _ := rfl }

/-- The inclusion of the bounded functions into the continuous functions to `E` becomes an
isomorphism after sheafification: every continuous function is bounded on affine opens, which
are quasi-compact. -/
lemma w_boundedToContinuousMap :
    letI := normedFieldOfAlgebra l E
    (ProEt.topology X).W (boundedToContinuousMap X l E) := by
  let := normedFieldOfAlgebra l E
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  refine ⟨Presheaf.isLocallyInjective_of_injective _ _ fun U x y h ↦ ?_,
    ⟨fun {U} s ↦ ?_⟩⟩
  · obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have h' : (x : C(U.unop.left, E)) = y :=
      congrArg (fun z : ULift.{u + 1} C(U.unop.left, E) ↦ z.down) h
    rw [Subtype.ext h']
  · refine ProEt.mem_topology_of_isOpenImmersion U _
      (fun i : U.left.affineOpens ↦
        overOpens (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U i.1)
      (fun i ↦ overOpensι (P := @WeaklyEtale) (fun _ _ ↦ inferInstance) U i.1) (fun i ↦ by
        exact inferInstanceAs (IsOpenImmersion i.1.ι)) (fun x ↦ ?_) fun i ↦ ?_
    · obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1
        U.left.isBasis_affineOpens) (show x ∈ (⊤ : U.left.Opens) from trivial)
      exact ⟨⟨W, hW⟩, ⟨x, hxW⟩, rfl⟩
    · have : CompactSpace (i.1 : U.left.Opens) :=
        isCompact_iff_compactSpace.1 i.2.isCompact
      exact ⟨ULift.up ⟨s.down.comp i.1.ι.base.hom,
        mem_boundedContinuousMaps_of_compactSpace l E (T := (i.1 : U.left.Opens)) _⟩, rfl⟩

/-- The cocone `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ E_X` over the tower `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`. -/
noncomputable def padicSubfieldSheafCocone :
    letI := normedFieldOfAlgebra l E
    Cocone (padicIntegersSheafMulSequence X l E) :=
  letI := normedFieldOfAlgebra l E
  { pt := continuousMapAbSheaf X E
    ι := NatTrans.ofSequence
      (fun n ↦ { hom := boundedOfIntegersPresheafHom X l E n ≫ boundedToContinuousMap X l E })
      fun n ↦ by
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine (sheafToPresheaf _ _).map_injective ?_
        refine ((sheafToPresheaf _ _).map_comp _ _).trans ?_
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ boundedToContinuousMap X l E)
          ((boundedPresheafCocone X l E).w (homOfLE (n.le_add_right 1)))) }

/-- **`E_X = 𝒪_{E,X}[1/ℓ]`**: the abelian sheaf `E_X = C(-, E)` is the colimit of the tower
`𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯`. The presheaf colimit is the presheaf of bounded functions
(`AlgebraicGeometry.ProEtale.isColimitBoundedPresheafCocone`), whose sheafification is `E_X`
(`AlgebraicGeometry.ProEtale.w_boundedToContinuousMap`). -/
noncomputable def isColimitPadicSubfieldSheafCocone :
    letI := normedFieldOfAlgebra l E
    IsColimit (padicSubfieldSheafCocone X l E) := by
  let := normedFieldOfAlgebra l E
  have := ((ProEt.topology X).W_iff _).1 (w_boundedToContinuousMap X l E)
  let D := padicIntegersSheafMulSequence X l E
  let α : (D ⋙ sheafToPresheaf _ _) ⋙ presheafToSheaf _ _ ≅ D :=
    NatIso.ofComponents (fun n ↦ asIso ((sheafificationAdjunction _ _).counit.app (D.obj n)))
      fun f ↦ (sheafificationAdjunction _ _).counit.naturality (D.map f)
  refine (IsColimit.precomposeHomEquiv α _).1 ?_
  refine IsColimit.ofIsoColimit (isColimitOfPreserves (presheafToSheaf _ Ab.{u + 1})
    (isColimitBoundedPresheafCocone X l E)) (Cocone.ext
      (asIso ((presheafToSheaf _ _).map (boundedToContinuousMap X l E)) ≪≫
        asIso ((sheafificationAdjunction _ _).counit.app (continuousMapAbSheaf X E))) fun n ↦ ?_)
  have h := (sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).counit.naturality
    ((padicSubfieldSheafCocone X l E).ι.app n)
  simp only [Functor.comp_map, Functor.id_map] at h
  simp only [Functor.mapCocone_ι_app, Iso.trans_hom, asIso_hom, Cocone.precompose_obj_ι,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, α, ← Functor.map_comp_assoc]
  refine Eq.trans ?_ h
  rfl

end AlgebraicGeometry.ProEtale
