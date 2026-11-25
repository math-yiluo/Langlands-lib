/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeIntegralSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeRetract
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeConjugate
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeDescentCriterion
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeDescentMap
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.GLValues
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRationalizationRegular

/-!
# The rationalised lattice of an integral cocycle is a descent

Let `f : V ⟶ T` be a single-morphism pro-étale cover and `γ` a continuous integral cocycle on
`V ×_T V`. The extension of scalars `ℚ̄_ℓ ⊗ M` of the lattice `M` of `γ`
(`AlgebraicGeometry.integralCocycleLattice`) is trivialised over `V`, and it is the descent of
`ℚ̄_ℓ,Vᴺ` along the matrix `γ⁻¹`
(`AlgebraicGeometry.ProEtale.nonempty_iso_descentSheaf_integralCocycleLattice`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

/-- An integral cocycle is inverted by the symmetry of `V ×_T V`. -/
lemma IsIntegralCocycle.apply_pullbackSymmetry (hγ : IsIntegralCocycle f γ)
    (z : ↥(pullback f f)) : γ ((pullbackSymmetry f f).hom.base z) = (γ z)⁻¹ := by
  let t : pullback f f ⟶ tripleProduct f :=
    pullback.lift (pullbackSymmetry f f).hom (𝟙 _) (by simp)
  have h₁₂ : t ≫ pullback.fst (pullback.snd f f) (pullback.fst f f) =
      (pullbackSymmetry f f).hom := pullback.lift_fst _ _ _
  have h₂₃ : t ≫ pullback.snd (pullback.snd f f) (pullback.fst f f) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have h₁₃ : t ≫ tripleProj₁₃ f = pullback.snd f f ≫ pullback.diagonal f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, h₁₂, Category.assoc,
        pullback.diagonal_fst, Category.comp_id, pullbackSymmetry_hom_comp_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h₂₃, Category.id_comp,
        Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have e₁₂ := congrArg (fun φ ↦ φ.base z) h₁₂
  have e₂₃ := congrArg (fun φ ↦ φ.base z) h₂₃
  have e₁₃ := congrArg (fun φ ↦ φ.base z) h₁₃
  simp only [Scheme.Hom.comp_apply] at e₁₂ e₂₃ e₁₃
  have := hγ.cocycle (t.base z)
  rw [e₁₃, e₁₂, e₂₃, hγ.diagonal] at this
  exact eq_inv_of_mul_eq_one_left this.symm

/-- The two points `(p₁ w, t)` and `(p₂ w, t)` of `V ×_T P` of a point `(t, w)` of
`P ×_T (V ×_T V)`. -/
noncomputable abbrev descentPoint {P : Scheme.{u}} (π : P ⟶ T) (p : pullback f f ⟶ V)
    (hp : p ≫ f = pullback.fst f f ≫ f) : pullback π (pullback.fst f f ≫ f) ⟶ pullback f π :=
  pullback.lift (pullback.snd π (pullback.fst f f ≫ f) ≫ p) (pullback.fst _ _) (by
    rw [Category.assoc, hp]
    exact pullback.condition.symm)

/-- **Twisted sections at the two points of a point of `P ×_T (V ×_T V)`**: they differ by the
cocycle at the swapped point. -/
lemma IsTwistedSection.apply_descentPoint {S : Type*} {c : ↥(pullback f f) → S → S}
    {P : Scheme.{u}} {π : P ⟶ T} {σ : ↥(pullback f π) → S} (hσ : IsTwistedSection f c π σ)
    (w : ↥(pullback π (pullback.fst f f ≫ f))) :
    σ ((descentPoint π (pullback.snd f f) pullback.condition.symm).base w) =
      c ((pullbackSymmetry f f).hom.base ((pullback.snd π (pullback.fst f f ≫ f)).base w))
        (σ ((descentPoint π (pullback.fst f f) rfl).base w)) := by
  let L : pullback π (pullback.fst f f ≫ f) ⟶
      pullback (pullback.snd f π) (pullback.snd f π) :=
    pullback.lift (descentPoint π (pullback.snd f f) pullback.condition.symm)
      (descentPoint π (pullback.fst f f) rfl) (by simp)
  have h₁ : L ≫ pullback.fst _ _ = descentPoint π (pullback.snd f f) pullback.condition.symm :=
    pullback.lift_fst _ _ _
  have h₂ : L ≫ pullback.snd _ _ = descentPoint π (pullback.fst f f) rfl :=
    pullback.lift_snd _ _ _
  have h₃ : L ≫ twistedPairMap f π =
      pullback.snd π (pullback.fst f f ≫ f) ≫ (pullbackSymmetry f f).hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, h₁, pullback.lift_fst,
        Category.assoc, pullbackSymmetry_hom_comp_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, h₂, pullback.lift_fst,
        Category.assoc, pullbackSymmetry_hom_comp_snd]
  have e₁ := congrArg (fun φ ↦ φ.base w) h₁
  have e₂ := congrArg (fun φ ↦ φ.base w) h₂
  have e₃ := congrArg (fun φ ↦ φ.base w) h₃
  simp only [Scheme.Hom.comp_apply] at e₁ e₂ e₃
  have := hσ.2 (L.base w)
  rw [e₁, e₂, e₃] at this
  exact this

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

open PadicAlgCl AdicSheaf Scheme

variable {l : ℕ} [Fact l.Prime] {T V : Scheme.{u}} {f : V ⟶ T} {N : ℕ}
  {γ : ↥(pullback f f) → GL (Fin N) ℤ_[l]}

variable (l) in
/-- The matrix of locally finite functions `z ↦ γ(z)⁻¹` of an integral cocycle. -/
noncomputable def integralCocycleInvMatrix (hγ : IsIntegralCocycle f γ) :
    Matrix (Fin N) (Fin N) (locallyFiniteFunctions l ↥(pullback f f)) :=
  Matrix.of fun i j ↦ integralToLocallyFiniteFunctions l _
    ⟨fun z ↦ (((γ z)⁻¹ : GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]) i j,
      hγ.continuous_inv i j⟩

/-- The values of `AlgebraicGeometry.ProEtale.integralCocycleInvMatrix`. -/
lemma integralCocycleInvMatrix_map_eval (hγ : IsIntegralCocycle f γ) (z : ↥(pullback f f)) :
    (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsEval z) =
      (((γ z)⁻¹ : GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]).map
        (padicIntToPadicAlgCl l) :=
  Matrix.ext fun _ _ ↦ rfl

/-- The entries of `AlgebraicGeometry.ProEtale.integralCocycleInvMatrix`. -/
lemma locallyFiniteFunctionsEval_integralCocycleInvMatrix (hγ : IsIntegralCocycle f γ)
    (z : ↥(pullback f f)) (i j : Fin N) :
    locallyFiniteFunctionsEval z (integralCocycleInvMatrix l hγ i j) =
      padicIntToPadicAlgCl l ((((γ z)⁻¹ : GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]) i j) :=
  rfl

/-- The matrix `γ⁻¹` is trivial on the diagonal. -/
lemma integralCocycleInvMatrix_map_diagonal (hγ : IsIntegralCocycle f γ) :
    (integralCocycleInvMatrix l hγ).map
      (locallyFiniteFunctionsComp l (pullback.diagonal f).base.hom) = 1 := by
  refine matrix_ext_locallyFiniteFunctionsEval fun v ↦ ?_
  rw [map_locallyFiniteFunctionsComp_map_eval, integralCocycleInvMatrix_map_eval]
  simp [hγ.diagonal, Matrix.map_one _ (map_zero _) (map_one _)]

/-- The cocycle condition for the matrix `γ⁻¹`. -/
lemma integralCocycleInvMatrix_map_tripleProj₁₃ (hγ : IsIntegralCocycle f γ) :
    (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l (tripleProj₁₃ f).base.hom) =
      (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd f f) (pullback.fst f f)).base.hom) *
      (integralCocycleInvMatrix l hγ).map (locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd f f) (pullback.fst f f)).base.hom) := by
  refine matrix_ext_locallyFiniteFunctionsEval fun w ↦ ?_
  rw [Matrix.map_mul, map_locallyFiniteFunctionsComp_map_eval,
    map_locallyFiniteFunctionsComp_map_eval, map_locallyFiniteFunctionsComp_map_eval,
    integralCocycleInvMatrix_map_eval, integralCocycleInvMatrix_map_eval,
    integralCocycleInvMatrix_map_eval, ← Matrix.map_mul, ← Units.val_mul, ← mul_inv_rev,
    ← hγ.cocycle]

section Values

omit [Fact l.Prime] in
/-- Locally finite functions are determined by their values. -/
lemma locallyFiniteFunctions_ext_eval [Fact l.Prime] {X : Type*} [TopologicalSpace X]
    {a b : locallyFiniteFunctions l X}
    (h : ∀ t, locallyFiniteFunctionsEval t a = locallyFiniteFunctionsEval t b) : a = b :=
  Subtype.ext (ContinuousMap.ext h)

/-- The values of a composed locally finite function. -/
lemma locallyFiniteFunctionsEval_comp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (c : C(X, Y)) (a : locallyFiniteFunctions l Y) (t : X) :
    locallyFiniteFunctionsEval t (locallyFiniteFunctionsComp l c a) =
      locallyFiniteFunctionsEval (c t) a :=
  rfl

/-- The values of an integral function. -/
lemma locallyFiniteFunctionsEval_integralToLocallyFiniteFunctions {X : Type*}
    [TopologicalSpace X] (g : C(X, ℤ_[l])) (t : X) :
    locallyFiniteFunctionsEval t (integralToLocallyFiniteFunctions l X g) =
      padicIntToPadicAlgCl l (g t) :=
  rfl

/-- The identification `ℤ_ℓ ⧸ ℓᵏ ≃ ℤ/ℓᵏ` is multiplicative. -/
lemma towerEquiv_smul (k : ℕ) (a : ℤ_[l]) (x : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :
    towerEquiv l k ((ULift.up a : ULift.{u + 1} ℤ_[l]) • x) =
      PadicInt.toZModPow k a * towerEquiv l k x := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have e₁ : (ULift.up a : ULift.{u + 1} ℤ_[l]) • Ideal.Quotient.mk (towerIdeal.{u} l k) b =
      towerReduce l k (a * b.down) := rfl
  have e₂ : Ideal.Quotient.mk (towerIdeal.{u} l k) b = towerReduce l k b.down := rfl
  rw [e₁, e₂, padicIntQuotientSpanPowAddEquiv_towerReduce,
    padicIntQuotientSpanPowAddEquiv_towerReduce, map_mul]

/-- The first point of `T' ×_T (V ×_T V)`, swapped. -/
lemma descentρ₁_comp_pullbackSymmetry_hom (T' : T.ProEt) :
    descentρ₁ f T' ≫ (pullbackSymmetry T'.hom f).hom =
      descentPoint T'.hom (pullback.fst f f) rfl := by
  apply pullback.hom_ext <;> simp [descentρ₁, descentPoint]

/-- The second point of `T' ×_T (V ×_T V)`, swapped. -/
lemma descentρ₂_comp_pullbackSymmetry_hom (T' : T.ProEt) :
    descentρ₂ f T' ≫ (pullbackSymmetry T'.hom f).hom =
      descentPoint T'.hom (pullback.snd f f) pullback.condition.symm := by
  apply pullback.hom_ext <;> simp [descentρ₂, descentPoint]

end Values

section Triv

variable [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f]

/-- **The trivialisation of the rationalised lattice** of an integral cocycle over the cover:
`f^* (ℚ̄_ℓ ⊗ M) ≅ ℚ̄_ℓ ⊗ f^* M ≅ ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ≅ ℚ̄_ℓ,Vᴺ`. -/
noncomputable def integralCocycleLatticeTriv (hγ : IsIntegralCocycle f γ) :
    (f)^*ᵃ[l].obj ((adicSheafExtendScalars T l).obj (integralCocycleLattice l hγ)) ≅
      ⨁ fun _ : Fin N ↦ AdicSheaf.unit l V :=
  ((padicIntModUpperStarCompAdicSheafExtendScalarsIso l f).app _).symm ≪≫
    (adicSheafExtendScalars V l).mapIso (upperStarIntegralCocycleLatticeIso hγ) ≪≫
    (adicSheafExtendScalars V l).mapBiproduct _ ≪≫
    biproduct.mapIso fun _ ↦ adicSheafExtendScalarsRegularIso l V

omit [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The adjoint of `ℚ̄_ℓ ⊗ ℤ_ℓ,V ≅ ℚ̄_ℓ,V` is the inclusion `ℤ_ℓ,V ⟶ ℚ̄_ℓ,V`. -/
lemma homEquiv_adicSheafExtendScalarsRegularIso_hom :
    ((adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
      (adicSheafExtendScalarsRegularIso l V).hom).hom = padicIntSheafToAdicConstantSheaf V l := by
  rw [Adjunction.homEquiv_unit, Mod.comp_hom']
  exact adicSheafExtendScalarsUnitAb_regular_comp l V

/-- The morphism `ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ⟶ ℚ̄_ℓ,Vᴺ` of the trivialisation. -/
noncomputable abbrev regularBiproductTriv :
    (adicSheafExtendScalars V l).obj (⨁ fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) ⟶
      ⨁ fun _ : Fin N ↦ AdicSheaf.unit l V :=
  ((adicSheafExtendScalars V l).mapBiproduct _).hom ≫
    (biproduct.mapIso fun _ ↦ adicSheafExtendScalarsRegularIso l V).hom

/-- **The adjoint of the trivialisation, restricted to `ℤ_ℓ`-modules**, computed through the
conjugate isomorphism. -/
lemma homEquiv_homEquiv_integralCocycleLatticeTriv_hom (hγ : IsIntegralCocycle f γ) :
    (adicSheafExtendScalarsRestrictAdjunction T l).homEquiv _ _
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (integralCocycleLatticeTriv hγ).hom) =
      (padicIntModUpperStarLowerStarAdjunction l f).homEquiv _ _
        ((upperStarIntegralCocycleLatticeIso hγ).hom ≫
          (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
            (regularBiproductTriv (l := l) (V := V) (N := N))) ≫
        (adicLowerStarRestrictPadicIntIso l f).inv.app _ := by
  rw [← Adjunction.homEquiv_naturality_left]
  exact Adjunction.homEquiv_homEquiv_pullIsoOfComapIso_inv
    (adicSheafExtendScalarsRestrictAdjunction V l) (adicSheafExtendScalarsRestrictAdjunction T l)
    (padicIntModUpperStarLowerStarAdjunction l f) (adicUpperStarLowerStarAdjunction l f)
    (adicLowerStarRestrictPadicIntIso l f) (integralCocycleLattice l hγ) _

omit [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The components of the adjoint of `ℚ̄_ℓ ⊗ ℤ_ℓ,Vᴺ ≅ ℚ̄_ℓ,Vᴺ`. -/
lemma homEquiv_regularBiproductTriv_comp_π (j : Fin N) :
    (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv
        (⨁ fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))
        (⨁ fun _ : Fin N ↦ AdicSheaf.unit l V)
        (regularBiproductTriv (l := l) (V := V) (N := N)) ≫
      (AdicSheaf.restrictPadicInt V l).map
        (biproduct.π (fun _ : Fin N ↦ AdicSheaf.unit l V) j) =
    biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j ≫
      (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv
        (Mod.regular (padicIntAbSheaf V l)) (AdicSheaf.unit l V)
        (adicSheafExtendScalarsRegularIso l V).hom := by
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
    regularBiproductTriv, Category.assoc, biproduct.mapIso_hom, biproduct.map_π,
    Functor.mapBiproduct_hom, biproduct.lift_π_assoc]

/-- The components of the free pullback of the lattice, as abelian sheaves. -/
lemma upperStarIntegralCocycleLatticeIso_hom_hom_π (hγ : IsIntegralCocycle f γ) (j : Fin N) :
    (upperStarIntegralCocycleLatticeIso hγ).hom.hom ≫
        (biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j).hom =
      (upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j := by
  have e : (upperStarIntegralCocycleLatticeIso hγ).hom.hom =
      (upperStarIntegralCocycleLatticeXIso hγ).hom ≫ ((Mod.forget _).mapBiproduct
        (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).inv := rfl
  have h : ((Mod.forget _).mapBiproduct
      (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).hom ≫ biproduct.π _ j =
      (Mod.forget _).map (biproduct.π _ j) := biproduct.lift_π _ _
  have h' : ((Mod.forget _).mapBiproduct
      (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l))).inv ≫
        (biproduct.π (fun _ : Fin N ↦ Mod.regular (padicIntAbSheaf V l)) j).hom =
      biproduct.π _ j := by
    rw [Iso.inv_comp_eq]
    exact h.symm
  rw [e, Category.assoc, h']
  rfl

/-- **The components of the trivialisation on sections**: the `j`-th component of the image of a
section `z` of `f^* M` is the `j`-th coordinate of `z`, an integral function. -/
lemma comps_homEquiv_regularBiproductTriv (hγ : IsIntegralCocycle f γ) (U : V.ProEt)
    (z : ((padicIntModUpperStar l f).obj (integralCocycleLattice l hγ)).X.obj.obj (op U))
    (j : Fin N) :
    comps (l := l) (B := V) (Z := U)
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N))).hom.hom.app (op U) z) j =
      integralToLocallyFiniteFunctions l _
        (((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j).hom.app (op U) z).down
    := by
  have e : comps (l := l) (B := V) (Z := U)
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N))).hom.hom.app (op U) z) j =
      (((upperStarIntegralCocycleLatticeIso hγ).hom ≫
        (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
          (regularBiproductTriv (l := l) (V := V) (N := N)) ≫
        (AdicSheaf.restrictPadicInt V l).map
          (biproduct.π (fun _ : Fin N ↦ AdicSheaf.unit l V) j)).hom.hom.app (op U) z).down := rfl
  rw [e, homEquiv_regularBiproductTriv_comp_π, ← Category.assoc, Mod.comp_hom', Mod.comp_hom',
    upperStarIntegralCocycleLatticeIso_hom_hom_π, homEquiv_adicSheafExtendScalarsRegularIso_hom,
    padicIntSheafToAdicConstantSheaf_eq]
  rfl

-- The defeq checks unfold the sections of composites of sheaf morphisms.
/-- **The coordinates of the trivialisation modulo `ℓᵏ`**: for a section `s` of the lattice over
`T'`, the `j`-th coordinate of its pullback to `T' ×_T V` is, modulo `ℓᵏ`, the `j`-th coordinate
of the twisted section of level `k` of `s` at the swapped point. -/
lemma toZModPow_upperStarIntegralCocycleLatticeXIso (hγ : IsIntegralCocycle f γ) (T' : T.ProEt)
    (s : (integralCocycleLattice l hγ).X.obj.obj (op T')) (k : ℕ) (j : Fin N)
    (u : ↥(pullback T'.hom f)) :
    PadicInt.toZModPow k ((((upperStarIntegralCocycleLatticeXIso hγ).hom ≫
      biproduct.π _ j).hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'))
        (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _).hom.app (op T') s)).down u) =
      towerEquiv l k ((((integralCocycleLatticeXIso hγ).hom ≫ limit.π _ (op k)).hom.app
        (op T') s).1 ((pullbackSymmetry T'.hom f).hom.base u) j) := by
  set U := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'
  have hu := Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction Ab.{u + 1} f)
    (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f inferInstance)
    (integralCocycleLattice l hγ).X
  have hR := localizationRestrictionIntegralCocycleLatticeXIso_hom_π hγ k j
  have ea : (upperStarIntegralCocycleLatticeXIso hγ).hom =
      (upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance).hom.app _ ≫
        (localizationRestrictionIntegralCocycleLatticeXIso hγ).hom := rfl
  have hu' : (upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _ ≫
      (f)_*[Ab.{u + 1}].map ((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j) =
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f inferInstance).unit.app _ ≫
        (f)_*[Ab.{u + 1}].map ((localizationRestrictionIntegralCocycleLatticeXIso hγ).hom ≫
          biproduct.π _ j) := by
    rw [ea, Category.assoc, Functor.map_comp, ← Category.assoc, upperStarIsoLocalizationRestriction,
      hu]
  have e1 := congrArg (fun φ ↦ ((φ.hom.app (op T')) s).down u) hu'
  have e2 := congrArg (fun φ ↦ ((φ.hom.app (op U))
    (((localizationRestrictionLowerStarAdjunction Ab.{u + 1} f inferInstance).unit.app
      (integralCocycleLattice l hγ).X).hom.app (op T') s)).down u) hR
  refine (congrArg (PadicInt.toZModPow k) e1).trans (e2.trans ?_)
  set g := (integralCocycleLatticeXIso hγ).hom ≫ limit.π (proEtIntegralCocycleTower γ ⋙
    sheafCompose (ProEt.topology T) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab)) (op k)
  set q := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstanceAs (WeaklyEtale f)) trivial).counit.app T'
  have hz := ConcreteCategory.congr_hom (localizationRestrictionLowerStarAdjunction_unit_app_hom_app
    Ab.{u + 1} f (inferInstanceAs (WeaklyEtale f)) (integralCocycleLattice l hγ).X (op T')) s
  have hn := NatTrans.naturality_apply g.hom q.op s
  have hm : frameSection f U.hom rfl ≫ pullbackMapRight f q.left (MorphismProperty.Over.w q) =
      (pullbackSymmetry T'.hom f).hom := by
    apply pullback.hom_ext
    · simp [q, U]
    · simp only [q, U, Functor.id_obj, Functor.comp_obj, Category.assoc, limit.lift_π,
        PullbackCone.mk_π_app, limit.lift_π_assoc, Functor.const_obj_obj,
        pullbackSymmetry_hom_comp_snd]
      exact Category.id_comp (pullback.fst T'.hom f)
  have hpt := congrArg (fun φ ↦ φ.base u) hm
  simp only [Scheme.Hom.comp_apply] at hpt
  erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    frameEvalHom_hom_app_apply]
  rw [ContinuousMap.coe_mk, frameCoord, frameEval, Function.comp_apply]
  erw [ProEtale.localizationRestriction_map_hom_app, hz, hn]
  exact congrArg (fun x ↦ towerEquiv l k ((g.hom.app (op T') s).1 x j)) hpt

omit [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The identification `Res (f_* B) ≅ f_* (Res B)` is the identity on underlying sheaves. -/
lemma adicLowerStarRestrictPadicIntIso_inv_app_hom (B : AdicSheaf l V) :
    ((adicLowerStarRestrictPadicIntIso l f).inv.app B).hom = 𝟙 _ := by
  simp [adicLowerStarRestrictPadicIntIso, adicLowerStarCompRestrictPadicIntIso,
    restrictPadicIntCompPadicIntModLowerStarIso]
  rfl

omit [Surjective f] [QuasiCompact f] [QuasiSeparated f] in
/-- The identification `Res (f_* B) ≅ f_* (Res B)` is the identity on sections. -/
lemma adicLowerStarRestrictPadicIntIso_inv_app_hom_app_apply (B : AdicSheaf l V) (T' : T.ProEt)
    (x : ((padicIntModLowerStar l f).obj ((AdicSheaf.restrictPadicInt V l).obj B)).X.obj.obj
      (op T')) :
    (((adicLowerStarRestrictPadicIntIso l f).inv.app B).hom.hom.app (op T')) x = x := by
  rw [adicLowerStarRestrictPadicIntIso_inv_app_hom]
  rfl

set_option maxRecDepth 20000 in
-- The sections of composites of sheaf morphisms are unfolded.
/-- The adjoint of the trivialisation, restricted to `ℤ_ℓ`-modules, as a morphism of abelian
sheaves. -/
lemma homEquiv_comp_descentMap_hom (hγ : IsIntegralCocycle f γ) :
    ((adicSheafExtendScalarsRestrictAdjunction T l).homEquiv _ _
      ((adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (integralCocycleLatticeTriv hγ).hom) ≫
      (AdicSheaf.restrictPadicInt T l).map (descentMap f (integralCocycleInvMatrix l hγ))).hom =
      0 := by
  rw [homEquiv_homEquiv_integralCocycleLatticeTriv_hom, Mod.comp_hom', Mod.comp_hom',
    padicIntModUpperStarLowerStarAdjunction]
  erw [Adjunction.modAdjunction_homEquiv_apply_hom]
  rw [Adjunction.homEquiv_unit]
  set ψ := (upperStarIntegralCocycleLatticeIso hγ).hom ≫
    (adicSheafExtendScalarsRestrictAdjunction V l).homEquiv _ _
      (regularBiproductTriv (l := l) (V := V) (N := N)) with hψ
  refine comp_descentMap_eq_zero (integralCocycleInvMatrix l hγ) _
    (fun T' s j ↦ integralToLocallyFiniteFunctions l _
      ((((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'))
          (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _).hom.app (op T') s)).down))
    (fun T' s ↦ funext fun j ↦ by
      have h₁ := adicLowerStarRestrictPadicIntIso_inv_app_hom_app_apply (f := f)
        (⨁ fun _ : Fin N ↦ unit l V) T'
        (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _ ≫
          (f)_*[Ab.{u + 1}].map ψ.hom).hom.app (op T') s)
      have h₂ := comps_homEquiv_regularBiproductTriv hγ
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T')
        (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _).hom.app (op T') s) j
      exact (congrArg (fun x ↦ comps (l := l) (B := V)
        (Z := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T') x j) h₁).trans h₂)
    fun T' s i ↦ ?_
  refine locallyFiniteFunctions_ext_eval fun w ↦ ?_
  have key : ∑ j, (((γ ((pullback.snd T'.hom (pullback.fst f f ≫ f)).base w))⁻¹ :
      GL (Fin N) ℤ_[l]) : Matrix (Fin N) (Fin N) ℤ_[l]) i j *
      ((((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ j).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'))
          (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _).hom.app (op T') s)).down
            ((descentρ₁ f T').base w)) =
      ((((upperStarIntegralCocycleLatticeXIso hγ).hom ≫ biproduct.π _ i).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj T'))
          (((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app _).hom.app (op T') s)).down
            ((descentρ₂ f T').base w)) := by
    refine PadicInt.ext_of_toZModPow.1 fun k ↦ ?_
    rw [map_sum]
    simp only [map_mul]
    have hp₁ := congrArg (fun φ ↦ φ.base w) (descentρ₁_comp_pullbackSymmetry_hom (f := f) T')
    have hp₂ := congrArg (fun φ ↦ φ.base w) (descentρ₂_comp_pullbackSymmetry_hom (f := f) T')
    simp only [Scheme.Hom.comp_apply] at hp₁ hp₂
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ congrArg₂ (· * ·) rfl
      (toZModPow_upperStarIntegralCocycleLatticeXIso hγ T' s k j _)) ?_
    refine Eq.trans ?_ (toZModPow_upperStarIntegralCocycleLatticeXIso hγ T' s k i _).symm
    rw [hp₁, hp₂]
    have hσ := (mem_twistedSubmodule f _).1 (((integralCocycleLatticeXIso hγ).hom ≫
      limit.π (proEtIntegralCocycleTower γ ⋙ sheafCompose (ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab)) (op k)).hom.app (op T') s).2
    rw [hσ.apply_descentPoint w, levelCocycleInt_apply, levelCocycle_apply_eq_sum, map_sum]
    simp only [towerEquiv_smul, hγ.apply_pullbackSymmetry]
  have := congrArg (padicIntToPadicAlgCl l) key
  rw [map_sum] at this
  simp only [RingHom.map_mul] at this
  -- Pass the additive hom explicitly to avoid searching for a homomorphism class.
  refine (map_sum (locallyFiniteFunctionsEval (l := l) w).toAddMonoidHom _ _).trans ?_
  exact this

/-- **The rationalised lattice of an integral cocycle is a descent**: `ℚ̄_ℓ ⊗ M` is the descent
of `ℚ̄_ℓ,Vᴺ` along the matrix `γ⁻¹`. -/
theorem nonempty_iso_descentSheaf_integralCocycleLattice (hγ : IsIntegralCocycle f γ) :
    Nonempty ((adicSheafExtendScalars T l).obj (integralCocycleLattice l hγ) ≅
      descentSheaf f (integralCocycleInvMatrix l hγ)) := by
  set κ := (adicUpperStarLowerStarAdjunction l f).homEquiv _ _ (integralCocycleLatticeTriv hγ).hom
  have hκ : κ ≫ descentMap f (integralCocycleInvMatrix l hγ) = 0 := by
    apply ((adicSheafExtendScalarsRestrictAdjunction T l).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit _ _ _ 0, Functor.map_zero,
      comp_zero]
    exact Mod.Hom.ext (homEquiv_comp_descentMap_hom hγ)
  exact ⟨@asIso _ _ _ _ (kernel.lift _ κ hκ)
    (AdicSheaf.isIso_kernelLift (integralCocycleInvMatrix_map_diagonal hγ)
      (integralCocycleInvMatrix_map_tripleProj₁₃ hγ) κ hκ
      (by rw [Equiv.symm_apply_apply]; infer_instance))⟩

end Triv

end AlgebraicGeometry.ProEtale
