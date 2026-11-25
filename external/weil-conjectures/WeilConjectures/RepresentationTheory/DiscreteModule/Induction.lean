/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Tactic.Group

/-!
# Restriction and coinduction of discrete modules

Let `G` be a topological group and `K` an open subgroup. Restriction along `K ⟶ G` is an exact
functor `DiscreteModule G ⥤ DiscreteModule K`; its right adjoint is the coinduction
`N ↦ {f : G → N smooth | f (k * g) = k • f g}`, which is exact when `K` has finite index. The
`Ext`-adjunction then gives Shapiro's lemma `Hⁿ(G, Coind N) ≅ Hⁿ(K, N)`, and the trace
`Coind (Res M) ⟶ M` composed with the unit `M ⟶ Coind (Res M)` is multiplication by the index.

## Main definitions and statements

- `DiscreteModule.res`: restriction along a continuous homomorphism.
- `DiscreteModule.coind`: coinduction from an open subgroup.
- `DiscreteModule.resCoindAdjunction`: restriction is left adjoint to coinduction.
- `DiscreteModule.coindTrace`: the trace map `Coind (Res M) ⟶ M` for a subgroup of finite index.
- `DiscreteModule.unit_comp_coindTrace`: the composite `M ⟶ Coind (Res M) ⟶ M` is
  multiplication by the index.
-/

@[expose] public section

universe w u v

open CategoryTheory Limits Action

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{v} C]

lemma comp_mk₀_zsmul_id {X Y : C} {n : ℕ} (x : Ext X Y n) (r : ℤ) :
    x.comp (mk₀ (r • 𝟙 Y)) (add_zero n) = r • x := by
  have h0 (f : Y ⟶ Y) : addEquiv₀ (mk₀ f) = f := homEquiv₀.apply_symm_apply f
  have h1 : (mk₀ (r • 𝟙 Y) : Ext Y Y 0) = r • mk₀ (𝟙 Y) :=
    addEquiv₀.injective (by rw [map_zsmul, h0, h0])
  have h2 := map_zsmul (x.precomp Y (add_zero n)) r (mk₀ (𝟙 Y))
  rw [h1]
  have h3 : (x.precomp Y (add_zero n)) (mk₀ (𝟙 Y)) = x := comp_mk₀_id x
  rw [h3] at h2
  exact h2

end CategoryTheory.Abelian.Ext

namespace DiscreteModule

/-- If `r` kills a discrete `G`-module `M`, then `r` kills its cohomology `Hⁿ(G, M)`. In
particular the cohomology of a module over `ℤ/r` is a `ℤ/r`-module.
(blueprint: `def-exc-continuous-cohomology`) -/
lemma zsmul_eq_zero_of_forall_zsmul_eq_zero {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : DiscreteModule.{w} G} {r : ℤ} (hM : ∀ m : M.obj.V, r • m = 0)
    {n : ℕ} (x : H G M n) : r • x = 0 := by
  have hzero : r • 𝟙 M = 0 := by
    apply (forget₂Ab.{w} G).map_injective
    rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero]
    ext m
    simp only [AddCommGrpCat.hom_zsmul, AddCommGrpCat.hom_id, AddCommGrpCat.hom_zero,
      AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.id_apply]
    exact hM m
  rw [← Abelian.Ext.comp_mk₀_zsmul_id, hzero, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]

section res

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Restriction of a discrete `G`-module along a continuous homomorphism `φ : H →* G`. -/
@[simps! obj_obj]
def res (φ : H →* G) (hφ : Continuous φ) : DiscreteModule.{w} G ⥤ DiscreteModule.{w} H :=
  ObjectProperty.lift _ (IsDiscreteModule.ι ⋙ Action.res _ φ) fun M x ↦
    (M.isOpen_stabilizer x).preimage hφ

variable (φ : H →* G) (hφ : Continuous φ)

instance : (res.{w} φ hφ).Additive where

instance : PreservesFiniteLimits (res.{w} φ hφ) :=
  have : PreservesFiniteLimits (res.{w} φ hφ ⋙ forget₂Ab.{w} H) :=
    inferInstanceAs (PreservesFiniteLimits (forget₂Ab.{w} G))
  preservesFiniteLimits_of_reflects_of_preserves _ (forget₂Ab.{w} H)

instance : PreservesFiniteColimits (res.{w} φ hφ) :=
  have : PreservesFiniteColimits (res.{w} φ hφ ⋙ forget₂Ab.{w} H) :=
    inferInstanceAs (PreservesFiniteColimits (forget₂Ab.{w} G))
  preservesFiniteColimits_of_reflects_of_preserves _ (forget₂Ab.{w} H)

/-- Restriction of the trivial module `ℤ` is the trivial module `ℤ`. -/
def resIntTrivialIso : (res.{w} φ hφ).obj (intTrivial G) ≅ intTrivial H :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun _ ↦ rfl)

end res

section coind

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)

/-- Restriction to a subgroup. -/
abbrev resSub : DiscreteModule.{w} G ⥤ DiscreteModule.{w} K :=
  res K.subtype continuous_subtype_val

variable {K}

/-- The smooth functions `f : G → N` with `f (k * g) = k • f g` for `k ∈ K`. -/
def coindSubgroup (N : DiscreteModule.{w} K) : AddSubgroup (smoothFunctions G N.obj.V) where
  carrier := {f | ∀ (k : K) (g : G), f.1 (k * g) = (N.obj.ρ k).asHom.hom (f.1 g)}
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ k g := by simp [h₁ k g, h₂ k g]
  neg_mem' {f} h k g := by simp [h k g]

/-- Right translation by `g` on coinduced functions. -/
def coindTranslate (N : DiscreteModule.{w} K) (g : G) : coindSubgroup N →+ coindSubgroup N :=
  ((translate g).comp (coindSubgroup N).subtype).codRestrict _ fun f k x ↦ by
    simpa [mul_assoc] using f.2 k (x * g)

@[simp]
lemma coindTranslate_apply (N : DiscreteModule.{w} K) (g : G) (f : coindSubgroup N) (x : G) :
    (coindTranslate N g f).1.1 x = f.1.1 (x * g) :=
  rfl

variable (K) in
/-- The coinduced action: the functions `f : G → N`, smooth and `K`-equivariant, with `G`
acting by right translation. -/
@[simps]
def coindAction (N : DiscreteModule.{w} K) : Action AddCommGrpCat.{max u w} G where
  V := AddCommGrpCat.of (coindSubgroup N)
  ρ :=
    { toFun g := .of <| AddCommGrpCat.ofHom (coindTranslate N g)
      map_one' := End.ext <| AddCommGrpCat.ext fun f ↦
        Subtype.ext (Subtype.ext (funext fun x ↦ by simp [End.one_asHom]))
      map_mul' a b := End.ext <| AddCommGrpCat.ext fun f ↦
        Subtype.ext (Subtype.ext (funext fun x ↦ by simp [End.mul_asHom, mul_assoc])) }

lemma coindAction_stabilizer (N : DiscreteModule.{w} K) (f : (coindAction K N).V) :
    (coindAction K N).stabilizer f = rightStab G f.1.1 := by
  ext g
  simp only [mem_stabilizer, mem_rightStab]
  change (coindTranslate N g f = f) ↔ _
  exact ⟨fun h x ↦ congr_fun (congrArg (fun f ↦ f.1.1) h) x,
    fun h ↦ Subtype.ext (Subtype.ext (funext h))⟩

variable (K) in
/-- The coinduction functor from discrete `K`-modules to discrete `G`-modules, right adjoint to
restriction (`DiscreteModule.resCoindAdjunction`). -/
@[simps obj]
def coind : DiscreteModule.{w} K ⥤ DiscreteModule.{w} G where
  obj N := ⟨coindAction K N, fun f ↦ by
    rw [coindAction_stabilizer]
    exact f.1.2⟩
  map {N N'} ψ := ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        (((smoothFunctionsMap ψ.hom.hom.hom).comp (coindSubgroup N).subtype).codRestrict _
          fun f k x ↦ by
            simp [f.2 k x, hom_comm_apply])
      comm g := rfl }

instance : (coind.{w} K).Additive where
  map_add := rfl

/-- The map `X ⟶ Coind N`, `x ↦ (g ↦ ψ (g • x))`, adjoint to `ψ : Res X ⟶ N`. -/
def coindLift {X : DiscreteModule.{w} G} {N : DiscreteModule.{w} K}
    (ψ : (resSub K).obj X ⟶ N) : X ⟶ (coind K).obj N :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun x := ⟨⟨fun g ↦ ψ.hom.hom.hom ((X.obj.ρ g).asHom.hom x), Subgroup.isOpen_mono
            (H₁ := X.obj.stabilizer x) (fun u hu y ↦ by simp [mem_stabilizer.1 hu])
            (X.isOpen_stabilizer x)⟩, fun k g ↦ by
              simp only [ρ_mul_apply]
              exact hom_comm_apply ψ.hom k ((X.obj.ρ g).asHom.hom x)⟩
          map_zero' := by ext; simp
          map_add' _ _ := by ext; simp }
      comm g := AddCommGrpCat.ext fun x ↦ Subtype.ext (Subtype.ext (funext fun y ↦ by
        change ψ.hom.hom.hom ((X.obj.ρ y).asHom.hom ((X.obj.ρ g).asHom.hom x)) =
          ψ.hom.hom.hom ((X.obj.ρ (y * g)).asHom.hom x)
        simp)) }

@[simp]
lemma coindLift_apply {X : DiscreteModule.{w} G} {N : DiscreteModule.{w} K}
    (ψ : (resSub K).obj X ⟶ N) (x : X.obj.V) (g : G) :
    ((coindLift ψ).hom.hom.hom x).1.1 g = ψ.hom.hom.hom ((X.obj.ρ g).asHom.hom x) :=
  rfl

variable (K) in
/-- Evaluation at `1` on coinduced functions, a morphism of discrete `K`-modules. -/
def coindEval (N : DiscreteModule.{w} K) : (resSub K).obj ((coind K).obj N) ⟶ N :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun f := f.1.1 1
          map_zero' := rfl
          map_add' _ _ := rfl }
      comm k := AddCommGrpCat.ext fun f ↦ by
        change f.1.1 (1 * (k : G)) = (N.obj.ρ k).asHom.hom (f.1.1 1)
        rw [one_mul, ← f.2 k 1, mul_one] }

@[simp]
lemma coindEval_apply (N : DiscreteModule.{w} K) (f : ((coind K).obj N).obj.V) :
    (coindEval K N).hom.hom.hom f = f.1.1 1 :=
  rfl

variable (K) in
/-- Restriction is left adjoint to coinduction. -/
def resCoindAdjunction : resSub.{w} K ⊣ coind K :=
  Adjunction.mkOfHomEquiv
    { homEquiv X N :=
        { toFun := coindLift
          invFun F := (resSub K).map F ≫ coindEval K N
          left_inv ψ := by
            ext x
            change ψ.hom.hom.hom ((X.obj.ρ 1).asHom.hom x) = ψ.hom.hom.hom x
            simp
          right_inv F := by
            ext x
            refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
            change ((F.hom.hom.hom ((X.obj.ρ g).asHom.hom x))).1.1 1 = (F.hom.hom.hom x).1.1 g
            rw [hom_comm_apply]
            change (F.hom.hom.hom x).1.1 (1 * g) = _
            rw [one_mul] }
      homEquiv_naturality_left_symm f g := rfl
      homEquiv_naturality_right f g := rfl }

lemma resCoindAdjunction_unit_app_apply (M : DiscreteModule.{w} G) (x : M.obj.V) (g : G) :
    (((resCoindAdjunction K).unit.app M).hom.hom.hom x).1.1 g = (M.obj.ρ g).asHom.hom x :=
  rfl

instance : PreservesFiniteLimits (coind.{w} K) :=
  have := (resCoindAdjunction K).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

section finiteIndex

variable [K.FiniteIndex]

instance : Finite (Quotient (QuotientGroup.rightRel K)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel K).symm

variable (K) in
/-- A representative of the right coset `K g`. -/
noncomputable def cosetRep (g : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel K) g)

omit [TopologicalSpace G] [IsTopologicalGroup G] [K.FiniteIndex] in
lemma mul_inv_cosetRep_mem (g : G) : g * (cosetRep K g)⁻¹ ∈ K :=
  QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq
    (Quotient.mk (QuotientGroup.rightRel K) g)))

omit [TopologicalSpace G] [IsTopologicalGroup G] [K.FiniteIndex] in
lemma cosetRep_eq_of_mul_inv_mem {g g' : G} (h : g' * g⁻¹ ∈ K) :
    cosetRep K g' = cosetRep K g := by
  unfold cosetRep
  congr 1
  exact (Quotient.sound (QuotientGroup.rightRel_apply.2 h)).symm

omit [TopologicalSpace G] [IsTopologicalGroup G] [K.FiniteIndex] in
lemma cosetRep_eq_out (c : Quotient (QuotientGroup.rightRel K)) :
    cosetRep K c.out = c.out := by
  unfold cosetRep
  rw [Quotient.out_eq]


/-- For `K` open of finite index, coinduction preserves surjections. -/
lemma surjective_coind_map (hK : IsOpen (K : Set G)) {N N' : DiscreteModule.{w} K} (ψ : N ⟶ N')
    (hψ : Function.Surjective ψ.hom.hom.hom) :
    Function.Surjective ((coind K).map ψ).hom.hom.hom := by
  intro f'
  let n : G → N.obj.V := fun r ↦ Function.surjInv hψ (f'.1.1 r)
  let kk : G → K := fun g ↦ ⟨g * (cosetRep K g)⁻¹, mul_inv_cosetRep_mem g⟩
  let F : G → N.obj.V := fun g ↦ (N.obj.ρ (kk g)).asHom.hom (n (cosetRep K g))
  have hFk (k : K) (g : G) : F (k * g) = (N.obj.ρ k).asHom.hom (F g) := by
    have h1 : cosetRep K (k * g) = cosetRep K g :=
      cosetRep_eq_of_mul_inv_mem (by simp [mul_assoc])
    have h2 : kk (k * g) = k * kk g := Subtype.ext (by simp [kk, h1, mul_assoc])
    simp only [F, h1, h2, ρ_mul_apply]
  -- the open subgroup fixing `F`
  let V : Quotient (QuotientGroup.rightRel K) → Subgroup G := fun c ↦
    ((N.obj.stabilizer (n c.out)).map K.subtype).comap (MulAut.conj c.out).toMonoidHom
  have hV (c) : IsOpen (V c : Set G) := by
    have h1 : IsOpen (((N.obj.stabilizer (n c.out)).map K.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact hK.isOpenMap_subtype_val _ (N.isOpen_stabilizer _)
    exact h1.preimage (show Continuous fun v : G ↦ c.out * v * c.out⁻¹ by fun_prop)
  refine ⟨⟨⟨F, Subgroup.isOpen_mono (H₁ := ⨅ c, V c) ?_ ?_⟩, hFk⟩, ?_⟩
  · intro u hu g
    let c : Quotient (QuotientGroup.rightRel K) := Quotient.mk _ g
    have hc : cosetRep K g = c.out := rfl
    obtain ⟨σ, hσ, hσu⟩ := Subgroup.mem_iInf.1 hu c
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      Subgroup.coe_subtype] at hσu
    have h1 : cosetRep K (g * u) = cosetRep K g := by
      apply cosetRep_eq_of_mul_inv_mem
      have : g * u * g⁻¹ = (kk g : G) * σ * (kk g : G)⁻¹ := by
        simp only [kk, hσu, hc]
        group
      rw [this]
      exact K.mul_mem (K.mul_mem (kk g).2 σ.2) (K.inv_mem (kk g).2)
    have h2 : kk (g * u) = kk g * σ := Subtype.ext (by
      simp only [kk, h1, Subgroup.coe_mul, hσu, hc]
      group)
    simp only [F, h1, h2, ρ_mul_apply]
    rw [show (N.obj.ρ σ).asHom.hom (n (cosetRep K g)) = n (cosetRep K g) from hσ]
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hV
  · refine Subtype.ext (Subtype.ext (funext fun g ↦ ?_))
    change ψ.hom.hom.hom (F g) = f'.1.1 g
    simp only [F, n]
    rw [hom_comm_apply, Function.surjInv_eq hψ]
    have hf' := (show coindSubgroup N' from f').2 (kk g) (cosetRep K g)
    refine hf'.symm.trans ?_
    simp [kk]

lemma preservesEpimorphisms_coind (hK : IsOpen (K : Set G)) :
    (coind.{w} K).PreservesEpimorphisms where
  preserves {N N'} ψ _ := by
    refine (forget₂Ab.{w} G).epi_of_epi_map ?_
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_coind_map hK ψ
      ((AddCommGrpCat.epi_iff_surjective _).1 ((forget₂Ab.{w} K).map_epi ψ))

lemma preservesFiniteColimits_coind (hK : IsOpen (K : Set G)) :
    PreservesFiniteColimits (coind.{w} K) :=
  have : (coind.{w} K).PreservesEpimorphisms := preservesEpimorphisms_coind hK
  have : (coind.{w} K).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have := this.preservesCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Right multiplication by `g` on right cosets `K \ G`. -/
def rightCosetMul (g : G) :
    Quotient (QuotientGroup.rightRel K) ≃ Quotient (QuotientGroup.rightRel K) where
  toFun := Quotient.map' (· * g) fun a b h ↦ by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h
  invFun := Quotient.map' (· * g⁻¹) fun a b h ↦ by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h
  left_inv c := Quotient.inductionOn' c fun a ↦ by simp [Quotient.map'_mk'']
  right_inv c := Quotient.inductionOn' c fun a ↦ by simp [Quotient.map'_mk'']

variable (M : DiscreteModule.{w} G)

/-- The summand `h⁻¹ • f h` of the trace, which only depends on the right coset `K h`. -/
def traceTerm (f : ((coind K).obj ((resSub K).obj M)).obj.V)
    (c : Quotient (QuotientGroup.rightRel K)) : M.obj.V :=
  Quotient.liftOn' c (fun h ↦ (M.obj.ρ h⁻¹).asHom.hom (f.1.1 h)) fun a b hab ↦ by
    rw [QuotientGroup.rightRel_apply] at hab
    have := (show coindSubgroup ((resSub K).obj M) from f).2 ⟨b * a⁻¹, hab⟩ a
    simp only [inv_mul_cancel_right] at this
    change (M.obj.ρ a⁻¹).asHom.hom (f.1.1 a) = (M.obj.ρ b⁻¹).asHom.hom (f.1.1 b)
    rw [this]
    change _ = (M.obj.ρ b⁻¹).asHom.hom ((M.obj.ρ (b * a⁻¹)).asHom.hom (f.1.1 a))
    rw [← ρ_mul_apply]
    simp

omit [K.FiniteIndex] in
lemma traceTerm_mk (f : ((coind K).obj ((resSub K).obj M)).obj.V) (h : G) :
    traceTerm M f (Quotient.mk'' h) = (M.obj.ρ h⁻¹).asHom.hom (f.1.1 h) :=
  rfl

noncomputable local instance : Fintype (Quotient (QuotientGroup.rightRel K)) :=
  Fintype.ofFinite _

/-- The trace `Coind (Res M) ⟶ M`, `f ↦ ∑_{h ∈ K \ G} h⁻¹ • f h`, for `K` of finite index. -/
noncomputable def coindTrace : (coind K).obj ((resSub K).obj M) ⟶ M :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom
        { toFun f := ∑ c, traceTerm M f c
          map_zero' := by
            refine Finset.sum_eq_zero fun c _ ↦ Quotient.inductionOn' c fun h ↦ ?_
            simp only [traceTerm_mk]
            exact map_zero _
          map_add' f₁ f₂ := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun c _ ↦ Quotient.inductionOn' c fun h ↦ ?_
            simp only [traceTerm_mk]
            exact map_add _ _ _ }
      comm g := AddCommGrpCat.ext fun f ↦ by
        change ∑ c, traceTerm M (coindTranslate _ g f) c =
          (M.obj.ρ g).asHom.hom (∑ c, traceTerm M f c)
        rw [map_sum]
        conv_rhs => rw [← (rightCosetMul g).sum_comp]
        refine Finset.sum_congr rfl fun c _ ↦ Quotient.inductionOn' c fun h ↦ ?_
        change (M.obj.ρ h⁻¹).asHom.hom (f.1.1 (h * g)) =
          (M.obj.ρ g).asHom.hom ((M.obj.ρ (h * g)⁻¹).asHom.hom (f.1.1 (h * g)))
        rw [← ρ_mul_apply]
        simp }

/-- The composite `M ⟶ Coind (Res M) ⟶ M` of the unit and the trace is multiplication by the
index of `K`. -/
lemma unit_comp_coindTrace :
    (resCoindAdjunction K).unit.app M ≫ coindTrace M = (K.index : ℤ) • 𝟙 M := by
  ext x
  change ∑ c, traceTerm (K := K) M (((resCoindAdjunction K).unit.app M).hom.hom.hom x) c =
    (K.index : ℤ) • x
  have hterm (c : Quotient (QuotientGroup.rightRel K)) :
      traceTerm (K := K) M (((resCoindAdjunction K).unit.app M).hom.hom.hom x) c = x :=
    Quotient.inductionOn' c fun h ↦ by
      rw [traceTerm_mk, resCoindAdjunction_unit_app_apply, ρ_inv_apply_apply]
  rw [Finset.sum_congr rfl fun c _ ↦ hterm c]
  rw [Finset.sum_const, Finset.card_univ, natCast_zsmul, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel K).symm,
    Nat.card_eq_fintype_card]

/-- **Restriction–corestriction.** Let `K` be an open subgroup of finite index of `G` and `M` a
discrete `G`-module with `Hⁿ(K, M) = 0`. Then the index `[G : K]` kills `Hⁿ(G, M)`: the unit
`M ⟶ Coind (Res M)` followed by the trace is multiplication by the index, and
`Hⁿ(G, Coind (Res M)) ≅ Hⁿ(K, M)` by Shapiro's lemma (the `Ext`-adjunction for the exact
functors `Res ⊣ Coind`). -/
theorem index_zsmul_eq_zero (hK : IsOpen (K : Set G)) {n : ℕ}
    (h : Subsingleton (H K ((resSub K).obj M) n)) (x : H G M n) :
    (K.index : ℤ) • x = 0 := by
  have := preservesFiniteColimits_coind.{w} hK
  rw [← Abelian.Ext.comp_mk₀_zsmul_id, ← unit_comp_coindTrace, ← Abelian.Ext.mk₀_comp_mk₀,
    ← Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (by simp)]
  have hy : x.comp (Abelian.Ext.mk₀ ((resCoindAdjunction K).unit.app M)) (add_zero n) = 0 := by
    apply ((resCoindAdjunction K).extAddEquiv (intTrivial G) ((resSub K).obj M) n).injective
    rw [map_zero]
    have : Subsingleton (Abelian.Ext ((resSub K).obj (intTrivial G)) ((resSub K).obj M) n) := by
      refine ⟨fun a b ↦ ?_⟩
      let e := resIntTrivialIso.{w} K.subtype continuous_subtype_val
      rw [← Abelian.Ext.mk₀_id_comp a, ← Abelian.Ext.mk₀_id_comp b, ← e.hom_inv_id,
        ← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n)
        (by simp), Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by simp)]
      congr 1
      exact Subsingleton.elim _ _
    exact Subsingleton.elim _ _
  rw [hy, Abelian.Ext.zero_comp]

end finiteIndex

end coind

end DiscreteModule
