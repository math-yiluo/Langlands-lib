/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsFilteredColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapSections

/-!
# Global sections of `ℚ̲̄_ℓ,X` over a quasi-compact quasi-separated scheme

Let `X` be a scheme and `ℓ` a prime. For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the global
sections of the coefficient ring `E_X = p_X^* E̲` are the continuous maps `X → E`
(`AlgebraicGeometry.ProEtale.subfieldSectionRingEquiv`), through the comparison
`ψ_X : E_X ≅ C(-, E)_X` (`AlgebraicGeometry.ProEtale.isIso_continuousMapComparison`, Bhatt–Scholze,
*The pro-étale topology for schemes*, Lemma 4.2.12). If `X` is quasi-compact and
quasi-separated, global sections of `ℚ̄_ℓ,X = colim_E E_X` commute with this filtered colimit, so
the global sections of `ℚ̄_ℓ,X` are the continuous functions `X → ℚ̄_ℓ` with values in a finite
subextension (`AlgebraicGeometry.ProEtale.padicAlgClSectionRingEquiv`). These identifications are
compatible with pullback along morphisms of schemes, which on functions is precomposition
(`AlgebraicGeometry.ProEtale.Γ_map_condensedPullbackHom_padicAlgClSectionRingEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- A finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` is locally compact, being a finite-dimensional
normed space over the locally compact field `ℚ_ℓ`. -/
instance (E : FiniteIntermediateField ℓ) : LocallyCompactSpace E := by
  have : ProperSpace E := FiniteDimensional.proper ℚ_[ℓ] E
  infer_instance

/-! ### Global sections of `E_X` -/

section Subfield

variable (X : Scheme.{u}) (E : FiniteIntermediateField ℓ)

instance : IsIso (continuousMapComparison X E) :=
  isIso_continuousMapComparison X E

/-- The global sections of `E_X = p_X^* E̲` are the continuous maps `X → E`: the global section
of `C(-, E)_X` given by a continuous map, transported along `ψ_X⁻¹ : C(-, E)_X ≅ E_X`. -/
noncomputable def subfieldSectionRingHom :
    C(X, E) →+* Γ (padicSubfieldRingObj X ℓ E) :=
  (Γ.map (inv (continuousMapComparison X E))).comp (continuousMapSectionRingHom X E)

lemma subfieldSectionRingHom_bijective :
    Function.Bijective (subfieldSectionRingHom ℓ X E) := by
  rw [subfieldSectionRingHom, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ (continuousMapSectionRingHom_bijective X E)
  refine Function.bijective_iff_has_inverse.2 ⟨Γ.map (continuousMapComparison X E), fun s ↦ ?_,
    fun s ↦ ?_⟩ <;> exact Γ.ext (by simp)

/-- **The global sections of `E_X` are the continuous maps `X → E`.** -/
noncomputable def subfieldSectionRingEquiv : C(X, E) ≃+* Γ (padicSubfieldRingObj X ℓ E) :=
  RingEquiv.ofBijective _ (subfieldSectionRingHom_bijective ℓ X E)

variable {E} in
/-- The values at the unit section of the global sections of `E_X` given by continuous maps. -/
lemma unitHomEval_subfieldSectionRingHom (f : C(X, E)) :
    Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        (subfieldSectionRingHom ℓ X E f).hom =
      (inv (continuousMapComparison X E)).hom.app (op (ProEt.mk (𝟙 X)))
        (continuousMapRestrictRingHom X E (op (ProEt.mk (𝟙 X))) f) :=
  (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans
    (congrArg _ (unitHomEval_continuousMapSectionRingHom X E f))

/-- The inclusion `E ⊆ F` of finite subextensions, as a continuous map. -/
noncomputable def subfieldInclusion {E F : FiniteIntermediateField ℓ} (h : E ≤ F) : C(E, F) :=
  ⟨IntermediateField.inclusion h, continuous_subtype_val.subtype_mk _⟩

variable {E} in
/-- The global sections of `E_X` given by continuous maps are compatible with the inclusions
`E_X ⟶ F_X` for `E ≤ F`. -/
lemma Γ_map_padicSubfieldRingObjMap_subfieldSectionRingHom {F : FiniteIntermediateField ℓ}
    (h : E ≤ F) (f : C(X, E)) :
    Γ.map (padicSubfieldRingObjMap X ℓ h) (subfieldSectionRingHom ℓ X E f) =
      subfieldSectionRingHom ℓ X F ((subfieldInclusion ℓ h).comp f) := by
  have hn := continuousMapComparison_naturality X (IntermediateField.inclusion h).toRingHom
    (continuous_subtype_val.subtype_mk _)
  have hn' : inv (continuousMapComparison X E) ≫ padicSubfieldRingObjMap X ℓ h =
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (continuousMapRingSheafMap X (IntermediateField.inclusion h).toRingHom
          (continuous_subtype_val.subtype_mk _)) ≫ inv (continuousMapComparison X F) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
    rfl
  refine Γ.ext ?_
  rw [Γ.map_hom, subfieldSectionRingHom, subfieldSectionRingHom, RingHom.comp_apply,
    RingHom.comp_apply, Γ.map_hom, Γ.map_hom, Category.assoc, hn', ← Category.assoc]
  congr 1
  refine Sheaf.unitHomEval_injective (J := ProEt.topology X) (ProEt.isTerminalMkId X) _ ?_
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans ?_
  rw [unitHomEval_continuousMapSectionRingHom, unitHomEval_continuousMapSectionRingHom]
  rfl

end Subfield


/-! ### Global sections of `ℚ̄_ℓ,X` -/

section PadicAlgCl

variable (X : Scheme.{u})

variable {ℓ X} in
/-- Every section of `E_X` over `X` is the value at the unit section of a global section. -/
lemma exists_unitHomEval_eq {E : FiniteIntermediateField ℓ}
    (y : (padicSubfieldRingObj X ℓ E).obj.obj (op (ProEt.mk (𝟙 X)))) :
    ∃ f : C(X, E), Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
      (subfieldSectionRingHom ℓ X E f).hom = y := by
  refine ⟨((continuousMapComparison X E).hom.app (op (ProEt.mk (𝟙 X))) y).down, ?_⟩
  rw [unitHomEval_subfieldSectionRingHom]
  have h : continuousMapRestrictRingHom X E (op (ProEt.mk (𝟙 X)))
      ((continuousMapComparison X E).hom.app (op (ProEt.mk (𝟙 X))) y).down =
      (continuousMapComparison X E).hom.app (op (ProEt.mk (𝟙 X))) y :=
    ULift.ext (ContinuousMap.ext fun x ↦ rfl)
  rw [h]
  exact congrArg (fun φ ↦ φ.hom.app (op (ProEt.mk (𝟙 X))) y)
    (IsIso.hom_inv_id (continuousMapComparison X E))

/-- The ring homomorphism `Γ(E_X) →+* Γ(ℚ̄_ℓ,X)` induced by the inclusion `E_X ⟶ ℚ̄_ℓ,X`. -/
noncomputable abbrev subfieldToPadicAlgClSection (E : FiniteIntermediateField ℓ) :
    Γ (padicSubfieldRingObj X ℓ E) →+* Γ (padicAlgClRingObj X ℓ) :=
  Γ.map (padicSubfieldRingObjToPadicAlgCl X ℓ E)

variable {ℓ X} in
lemma subfieldToPadicAlgClSection_map {E F : FiniteIntermediateField ℓ} (h : E ≤ F)
    (t : Γ (padicSubfieldRingObj X ℓ E)) :
    subfieldToPadicAlgClSection ℓ X F (Γ.map (padicSubfieldRingObjMap X ℓ h) t) =
      subfieldToPadicAlgClSection ℓ X E t :=
  Γ.ext (by
    rw [Γ.map_hom, Γ.map_hom, Γ.map_hom, Category.assoc,
      padicSubfieldRingObjMap_comp_toPadicAlgCl])

section Qcqs

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- Over a quasi-compact quasi-separated scheme, the sections of `ℚ̄_ℓ,X = colim_E E_X` over `X`
are the filtered colimit of the sections of the `E_X`. -/
noncomputable def isColimitPadicAlgClRingObjSections :
    IsColimit ((Scheme.ProEt.abSectionsFunctor (ProEt.mk (𝟙 X))).mapCocone
      (padicAlgClRingObjCocone X ℓ)) :=
  have : CompactSpace (ProEt.mk (𝟙 X)).left := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (ProEt.mk (𝟙 X)).left := inferInstanceAs (QuasiSeparatedSpace X)
  Scheme.ProEt.isColimitSectionsOfIsColimitOfSmall (isColimitPadicAlgClRingObjCocone X ℓ) _

variable {ℓ X} in
/-- Every global section of `ℚ̄_ℓ,X` comes from a continuous map into a finite subextension. -/
lemma exists_subfieldToPadicAlgClSection_eq (s : Γ (padicAlgClRingObj X ℓ)) :
    ∃ (E : FiniteIntermediateField ℓ) (f : C(X, E)),
      subfieldToPadicAlgClSection ℓ X E (subfieldSectionRingHom ℓ X E f) = s := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  obtain ⟨E, y, hy⟩ := Concrete.isColimit_exists_rep _ (isColimitPadicAlgClRingObjSections ℓ X)
    (Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X)) s.hom)
  obtain ⟨f, rfl⟩ := exists_unitHomEval_eq y
  refine ⟨E, f, Γ.ext (Sheaf.unitHomEval_injective (J := ProEt.topology X)
    (ProEt.isTerminalMkId X) _ ?_)⟩
  rw [← hy]
  rfl

variable {ℓ X} in
/-- A global section of `E_X` vanishing in `ℚ̄_ℓ,X` vanishes in some `F_X`, `E ≤ F`. -/
lemma exists_map_eq_zero_of_subfieldToPadicAlgClSection_eq_zero {E : FiniteIntermediateField ℓ}
    (t : Γ (padicSubfieldRingObj X ℓ E)) (ht : subfieldToPadicAlgClSection ℓ X E t = 0) :
    ∃ (F : FiniteIntermediateField ℓ) (h : E ≤ F), Γ.map (padicSubfieldRingObjMap X ℓ h) t = 0 := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  obtain ⟨F, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq (i := E) (j := E) _
    (isColimitPadicAlgClRingObjSections ℓ X)
    (Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X)) t.hom) 0
    (by
      refine ((Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).symm.trans ?_).trans
        (map_zero _).symm
      change Sheaf.unitHomEval (J := ProEt.topology X) (ProEt.mk (𝟙 X))
        (subfieldToPadicAlgClSection ℓ X E t).hom = 0
      rw [ht]
      rfl)
  refine ⟨F, leOfHom a, Γ.ext (Sheaf.unitHomEval_injective (J := ProEt.topology X)
    (ProEt.isTerminalMkId X) _ ?_)⟩
  refine (Sheaf.unitHomEval_comp (J := ProEt.topology X) _ _ _).trans ?_
  refine hab.trans ((map_zero _).trans ?_)
  rfl

end Qcqs

/-- Two finite subextensions are contained in a third one. -/
lemma exists_le_le (E F : FiniteIntermediateField ℓ) : ∃ G, E ≤ G ∧ F ≤ G :=
  ⟨⟨E.1 ⊔ F.1, inferInstance⟩, le_sup_left (a := E.1), le_sup_right (a := E.1)⟩

variable {ℓ X} in
/-- A continuous function `X → ℚ̄_ℓ` with values in a finite subextension `E`, as a continuous
map `X → E`. -/
noncomputable def restrictSubfield (f : C(X, PadicAlgCl ℓ)) (E : FiniteIntermediateField ℓ)
    (hE : ∀ x, f x ∈ E.1) : C(X, E) :=
  ⟨fun x ↦ ⟨f x, hE x⟩, f.continuous.subtype_mk _⟩

variable {ℓ X} in
/-- The global section of `ℚ̄_ℓ,X` given by a continuous function with values in `E` does not
depend on the finite subextension `E ≤ F`. -/
lemma subfieldToPadicAlgClSection_restrictSubfield_of_le (f : C(X, PadicAlgCl ℓ))
    {E F : FiniteIntermediateField ℓ} (h : E ≤ F) (hE : ∀ x, f x ∈ E.1) (hF : ∀ x, f x ∈ F.1) :
    subfieldToPadicAlgClSection ℓ X F (subfieldSectionRingHom ℓ X F (restrictSubfield f F hF)) =
      subfieldToPadicAlgClSection ℓ X E
        (subfieldSectionRingHom ℓ X E (restrictSubfield f E hE)) := by
  rw [← subfieldToPadicAlgClSection_map h, Γ_map_padicSubfieldRingObjMap_subfieldSectionRingHom]
  rfl

variable {ℓ X} in
/-- The global section of `ℚ̄_ℓ,X` given by a continuous function with values in a finite
subextension does not depend on the finite subextension. -/
lemma subfieldToPadicAlgClSection_restrictSubfield_eq (f : C(X, PadicAlgCl ℓ))
    {E F : FiniteIntermediateField ℓ} (hE : ∀ x, f x ∈ E.1) (hF : ∀ x, f x ∈ F.1) :
    subfieldToPadicAlgClSection ℓ X F (subfieldSectionRingHom ℓ X F (restrictSubfield f F hF)) =
      subfieldToPadicAlgClSection ℓ X E
        (subfieldSectionRingHom ℓ X E (restrictSubfield f E hE)) := by
  obtain ⟨G, hEG, hFG⟩ := exists_le_le ℓ E F
  rw [← subfieldToPadicAlgClSection_restrictSubfield_of_le f hFG hF
      (fun x ↦ (hFG : F.1 ≤ G.1) (hF x)),
    subfieldToPadicAlgClSection_restrictSubfield_of_le f hEG hE]

variable {ℓ X} in
/-- The global section of `ℚ̄_ℓ,X` given by a continuous function `X → ℚ̄_ℓ` with values in a
finite subextension. -/
noncomputable def padicAlgClSectionFun (f : finiteIntermediateFieldValued ℓ X) :
    Γ (padicAlgClRingObj X ℓ) :=
  subfieldToPadicAlgClSection ℓ X ⟨f.2.choose, f.2.choose_spec.1⟩
    (subfieldSectionRingHom ℓ X _ (restrictSubfield f.1 _ f.2.choose_spec.2))

variable {ℓ X} in
lemma padicAlgClSectionFun_eq (f : finiteIntermediateFieldValued ℓ X)
    (E : FiniteIntermediateField ℓ) (hE : ∀ x, f.1 x ∈ E.1) :
    padicAlgClSectionFun f =
      subfieldToPadicAlgClSection ℓ X E
        (subfieldSectionRingHom ℓ X E (restrictSubfield f.1 E hE)) :=
  subfieldToPadicAlgClSection_restrictSubfield_eq f.1 _ _

variable {ℓ X} in
/-- Two functions with values in finite subextensions take values in a common one. -/
lemma exists_finiteIntermediateField_forall_mem (f g : finiteIntermediateFieldValued ℓ X) :
    ∃ E : FiniteIntermediateField ℓ, (∀ x, f.1 x ∈ E.1) ∧ ∀ x, g.1 x ∈ E.1 := by
  obtain ⟨E, hE, hfE⟩ := f.2
  obtain ⟨F, hF, hgF⟩ := g.2
  obtain ⟨G, hEG, hFG⟩ := exists_le_le ℓ (⟨E, hE⟩ : FiniteIntermediateField ℓ) ⟨F, hF⟩
  exact ⟨G, fun x ↦ (hEG : E ≤ G.1) (hfE x),
    fun x ↦ (hFG : F ≤ G.1) (hgF x)⟩

/-- The global sections of `ℚ̄_ℓ,X` given by continuous functions with values in finite
subextensions, as a ring homomorphism. -/
noncomputable def padicAlgClSectionRingHom :
    finiteIntermediateFieldValued ℓ X →+* Γ (padicAlgClRingObj X ℓ) where
  toFun := padicAlgClSectionFun
  map_one' := by
    rw [padicAlgClSectionFun_eq 1 ⟨⊥, inferInstance⟩ fun _ ↦ one_mem _]
    exact (congrArg _ (congrArg _ (ContinuousMap.ext fun _ ↦ rfl))).trans
      ((congrArg _ (map_one _)).trans (map_one _))
  map_mul' f g := by
    obtain ⟨E, hf, hg⟩ := exists_finiteIntermediateField_forall_mem f g
    rw [padicAlgClSectionFun_eq f E hf, padicAlgClSectionFun_eq g E hg,
      padicAlgClSectionFun_eq (f * g) E fun x ↦ mul_mem (hf x) (hg x), ← map_mul, ← map_mul]
    rfl
  map_zero' := by
    rw [padicAlgClSectionFun_eq 0 ⟨⊥, inferInstance⟩ fun _ ↦ zero_mem _]
    exact (congrArg _ (congrArg _ (ContinuousMap.ext fun _ ↦ rfl))).trans
      ((congrArg _ (map_zero _)).trans (map_zero _))
  map_add' f g := by
    obtain ⟨E, hf, hg⟩ := exists_finiteIntermediateField_forall_mem f g
    rw [padicAlgClSectionFun_eq f E hf, padicAlgClSectionFun_eq g E hg,
      padicAlgClSectionFun_eq (f + g) E fun x ↦ add_mem (hf x) (hg x), ← map_add, ← map_add]
    rfl

variable [CompactSpace X] [QuasiSeparatedSpace X]

lemma padicAlgClSectionRingHom_bijective : Function.Bijective (padicAlgClSectionRingHom ℓ X) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun f hf ↦ ?_, fun s ↦ ?_⟩
  · obtain ⟨E, hE, hfE⟩ := f.2
    change padicAlgClSectionFun f = 0 at hf
    rw [padicAlgClSectionFun_eq f ⟨E, hE⟩ hfE] at hf
    obtain ⟨F, h, hF⟩ := exists_map_eq_zero_of_subfieldToPadicAlgClSection_eq_zero _ hf
    rw [Γ_map_padicSubfieldRingObjMap_subfieldSectionRingHom,
      ← map_zero (subfieldSectionRingHom ℓ X F)] at hF
    have h0 := (subfieldSectionRingHom_bijective ℓ X F).1 hF
    exact Subtype.ext (ContinuousMap.ext fun x ↦
      congrArg (fun k : C(X, F) ↦ ((k x : F) : PadicAlgCl ℓ)) h0)
  · obtain ⟨E, f, rfl⟩ := exists_subfieldToPadicAlgClSection_eq s
    refine ⟨⟨⟨fun x ↦ ((f x : E.1) : PadicAlgCl ℓ), continuous_subtype_val.comp f.continuous⟩,
      E.1, E.2, fun x ↦ (f x).2⟩, ?_⟩
    exact padicAlgClSectionFun_eq _ E (fun x ↦ (f x).2)

/-- **The global sections of `ℚ̄_ℓ,X` over a quasi-compact quasi-separated scheme** are the
continuous functions `X → ℚ̄_ℓ` with values in a finite subextension of `ℚ̄_ℓ / ℚ_ℓ`. -/
noncomputable def padicAlgClSectionRingEquiv :
    finiteIntermediateFieldValued ℓ X ≃+* Γ (padicAlgClRingObj X ℓ) :=
  RingEquiv.ofBijective _ (padicAlgClSectionRingHom_bijective ℓ X)

end PadicAlgCl


/-! ### Compatibility with pullback -/

section Pullback

open Functor.LaxMonoidal

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

omit [Fact ℓ.Prime] in
/-- Composition of the ring homomorphisms induced on global sections. -/
lemma _root_.CategoryTheory.MonObj.Γ.map_map {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {R S U : C} [MonObj R] [MonObj S] [MonObj U]
    (φ : R ⟶ S) (ψ : S ⟶ U) [IsMonHom φ] [IsMonHom ψ] (s : Γ R) :
    Γ.map ψ (Γ.map φ s) = Γ.map (φ ≫ ψ) s :=
  Γ.ext (by simp)

omit [Fact ℓ.Prime] in
/-- Equal morphisms of algebra objects induce equal maps on global sections. -/
lemma _root_.CategoryTheory.MonObj.Γ.map_congr {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] [MonoidalPreadditive C] {R S : C} [MonObj R] [MonObj S] {φ φ' : R ⟶ S}
    [IsMonHom φ] [IsMonHom φ'] (h : φ = φ') (s : Γ R) : Γ.map φ s = Γ.map φ' s := by
  subst h
  rfl

omit [Fact ℓ.Prime] in
/-- The global sections induced by a lax monoidal functor are natural. -/
lemma _root_.CategoryTheory.MonObj.Γ.mapFunctor_map {C D : Type*} [Category* C]
    [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] [Category* D]
    [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D] (F : C ⥤ D) [F.LaxMonoidal]
    [F.Additive] {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ] (s : Γ R) :
    Γ.mapFunctor F (Γ.map φ s) = Γ.map (F.map φ) (Γ.mapFunctor F s) :=
  Γ.ext (by simp)

/-- The pullback of the global section of `E_X` given by a continuous map `f : X → E` is the
global section of `E_{X'}` given by `f ∘ g`. -/
lemma Γ_map_condensedPullbackHom_subfieldSectionRingHom (E : FiniteIntermediateField ℓ)
    (f : C(X, E)) :
    Γ.map (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (subfieldSectionRingHom ℓ X E f)) =
      subfieldSectionRingHom ℓ X' E (f.comp g.base.hom) := by
  have sq := upperStar_map_continuousMapComparison_comp_continuousMapPullbackHom g E
  have sq' : (g)^*[Ab.{u + 1}].map (inv (continuousMapComparison X E)) ≫
      condensedPullbackHom (Profinite.continuousMapRingObj.{u} E) g =
      continuousMapPullbackHom g E ≫ inv (continuousMapComparison X' E) := by
    rw [← cancel_epi ((g)^*[Ab.{u + 1}].map (continuousMapComparison X E)),
      ← Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, sq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [subfieldSectionRingHom, subfieldSectionRingHom, RingHom.comp_apply, RingHom.comp_apply,
    Γ.mapFunctor_map, Γ.map_map, Γ.map_congr sq', ← Γ.map_map,
    Γ_map_continuousMapPullbackHom_mapFunctor]

variable {ℓ} in
/-- The precomposition with `g : X' ⟶ X` of a continuous function `X → ℚ̄_ℓ` with values in a
finite subextension. -/
noncomputable def finiteIntermediateFieldValuedComp (f : finiteIntermediateFieldValued ℓ X) :
    finiteIntermediateFieldValued ℓ X' :=
  ⟨f.1.comp g.base.hom, by
    obtain ⟨E, hE, hfE⟩ := f.2
    exact ⟨E, hE, fun x ↦ hfE _⟩⟩

@[simp]
lemma finiteIntermediateFieldValuedComp_apply (f : finiteIntermediateFieldValued ℓ X) (x : X') :
    (finiteIntermediateFieldValuedComp g f : C(X', PadicAlgCl ℓ)) x =
      (f : C(X, PadicAlgCl ℓ)) (g x) :=
  rfl

/-- **Compatibility with pullback**: along `g : X' ⟶ X`, the global section of `ℚ̄_ℓ,X` given by
a continuous function `f : X → ℚ̄_ℓ` with values in a finite subextension pulls back to the
global section of `ℚ̄_ℓ,X'` given by `f ∘ g`. -/
lemma Γ_map_condensedPullbackHom_padicAlgClSectionRingHom
    (f : finiteIntermediateFieldValued ℓ X) :
    Γ.map (condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) g)
        (Γ.mapFunctor (g)^*[Ab.{u + 1}] (padicAlgClSectionRingHom ℓ X f)) =
      padicAlgClSectionRingHom ℓ X' (finiteIntermediateFieldValuedComp g f) := by
  obtain ⟨E, hE, hfE⟩ := f.2
  have nat : (g)^*[Ab.{u + 1}].map (padicSubfieldRingObjToPadicAlgCl X ℓ ⟨E, hE⟩) ≫
      condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) g =
      condensedPullbackHom
        (Profinite.continuousMapRingObj.{u} (⟨E, hE⟩ : FiniteIntermediateField ℓ)) g ≫
        padicSubfieldRingObjToPadicAlgCl X' ℓ ⟨E, hE⟩ :=
    (upperStarFromPointComp g).hom.naturality
      (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ ⟨E, hE⟩)
  change Γ.map _ (Γ.mapFunctor _ (padicAlgClSectionFun f)) =
    padicAlgClSectionFun (finiteIntermediateFieldValuedComp g f)
  rw [padicAlgClSectionFun_eq f ⟨E, hE⟩ hfE,
    padicAlgClSectionFun_eq (finiteIntermediateFieldValuedComp g f) ⟨E, hE⟩ fun x ↦ hfE _,
    Γ.mapFunctor_map, Γ.map_map, Γ.map_congr nat, ← Γ.map_map,
    Γ_map_condensedPullbackHom_subfieldSectionRingHom]
  rfl

end Pullback

end AlgebraicGeometry.ProEtale
