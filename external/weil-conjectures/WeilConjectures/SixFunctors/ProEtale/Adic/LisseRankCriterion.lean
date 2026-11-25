/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.StrictLocalizationPoints
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseAbelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRank
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedFieldExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The fibre functor of `ℓ`-adic sheaves at a geometric point

For a point `s : Spec Ω ⟶ T` the *fibre functor* `M ↦ Γ(Spec Ω, s^* M)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.fibre`) is additive and left exact; if `Ω` is
algebraically closed it preserves epimorphisms, hence homology. It is the first step of a rank
criterion for lisse cohomology sheaves: the pointwise ranks of the differentials of a complex of
finite free sheaves are the ranks of the fibres of these differentials. The fibre of the
pullback along `p` is the fibre at the composite point
(`AlgebraicGeometry.ProEtale.AdicSheaf.fibreUpperStarIso`), and the fibre of `ℚ̄_ℓ,T` is
one-dimensional (`AlgebraicGeometry.ProEtale.AdicSheaf.finrank_fibre_unit`).

The fibre of an endomorphism `φ` of `ℚ̄_ℓ,T`, a locally finite function `f`, is multiplication by
`f(t)`, `t` the image of `s` (`AlgebraicGeometry.ProEtale.AdicSheaf.fibre_map_unit_apply`): the
restriction to `s` of the section given by `f` is the constant `f(t)`. Consequently the fibre of
a morphism `ψ : ℚ̄_ℓ,Tᵃ ⟶ ℚ̄_ℓ,Tᵇ` is, in the coordinates
`AlgebraicGeometry.ProEtale.AdicSheaf.fibreFreeCoord`, the matrix of `ψ` evaluated at `t`
(`AlgebraicGeometry.ProEtale.AdicSheaf.fibreFreeCoord_map`), and the rank of the fibre of `ψ` is
the pointwise rank of `ψ` at `t`
(`AlgebraicGeometry.ProEtale.AdicSheaf.finrank_range_fibre_map`).

## Main results

- `AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_homology_of_isLocallyConstant`: the
  homology of a short complex of finite free sheaves whose maps have locally constant pointwise
  ranks is lisse.
- `AlgebraicGeometry.ProEtale.AdicSheaf.finrank_fibre_homology`: the dimension of the fibre of
  the homology at a geometric point is the rank of the middle term minus the pointwise ranks of
  the two maps.
- `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_of_isIso_homology_free` and
  `AlgebraicGeometry.ProEtale.isAdicLisseSheaf_homology_of_locally_free`: on a locally
  Noetherian scheme, a complex which is pro-étale locally a bounded above complex of finite free
  sheaves has lisse cohomology sheaves. The fibre dimensions of the cohomology descend to the
  base and are constant along specializations, hence locally constant, and descending
  induction makes the pointwise ranks of the differentials locally constant.

This reduces the local constancy of the higher direct images along a smooth proper morphism to
the local perfectness of `Rf_* F`, which is not available here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T : Scheme.{u}} {Ω : Type u} [Field Ω]

namespace AdicSheaf

variable (l) in
/-- The fibre functor `M ↦ Γ(Spec Ω, s^* M)` at a point `s : Spec Ω ⟶ T`, with values in
`ℚ̄_ℓ`-modules. -/
noncomputable def fibre (s : Spec (.of Ω) ⟶ T) : AdicSheaf l T ⥤ WeilCoefficients.{u} l :=
  (s)^*ᵃ[l] ⋙ AdicSheaf.forget _ ⋙ Sheaf.Γ _ _

/-- The fibre functor is additive. -/
instance (s : Spec (.of Ω) ⟶ T) : (fibre l s).Additive := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  unfold fibre
  infer_instance

/-- The fibre functor is left exact. -/
instance (s : Spec (.of Ω) ⟶ T) : PreservesFiniteLimits (fibre l s) := by
  unfold fibre
  infer_instance

/-- At a geometric point the fibre functor preserves epimorphisms. -/
instance [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) : (fibre l s).PreservesEpimorphisms := by
  unfold fibre
  infer_instance

/-- At a geometric point, the fibre functor preserves homology: it preserves kernels and
epimorphisms. -/
instance [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) : (fibre l s).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The fibre of a pullback `p^* M` at `s` is the fibre of `M` at `s ≫ p`. -/
noncomputable def fibreUpperStarIso {T' : Scheme.{u}} (p : T' ⟶ T) (s : Spec (.of Ω) ⟶ T') :
    (p)^*ᵃ[l] ⋙ fibre l s ≅ fibre l (s ≫ p) :=
  (Functor.isoWhiskerRight (adicUpperStarComp l s p)
    (AdicSheaf.forget _ ⋙ Sheaf.Γ _ _)).symm

/-- The fibre of the constant sheaf `ℚ̄_ℓ,T` at any point is one-dimensional. -/
theorem finrank_fibre_unit (s : Spec (.of Ω) ⟶ T) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((fibre l s).obj (unit l T))) = 1 :=
  (WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
    ((AdicSheaf.forget _).mapIso (adicUpperStarUnitIso l s)))).finrank_eq.trans
      (finrank_globalSections_adicConstantSheaf (Spec (.of Ω)))

/-- The fibre of the finite free sheaf `ℚ̄_ℓ,Tⁿ` at any point is `n`-dimensional. -/
theorem finrank_fibre_free (s : Spec (.of Ω) ⟶ T) (n : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((fibre l s).obj (⨁ fun _ : Fin n ↦ unit l T))) = n := by
  have : (Sheaf.Γ (Scheme.ProEt.topology (Spec (.of Ω))) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := fibre l s ⋙ WeilCoefficients.toModuleCat l
  let e : G.obj (⨁ fun _ : Fin n ↦ unit l T) ≅
      ModuleCat.of _ (Fin n → G.obj (unit l T)) :=
    G.mapBiproduct (fun _ : Fin n ↦ unit l T) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (unit l T))
  have h1 : Module.finrank (PadicAlgCl l) (G.obj (unit l T)) = 1 := finrank_fibre_unit s
  have : FiniteDimensional (PadicAlgCl l) (G.obj (unit l T)) :=
    Module.finite_of_finrank_eq_succ h1
  calc _ = Module.finrank (PadicAlgCl l) (Fin n → G.obj (unit l T)) :=
        e.toLinearEquiv.finrank_eq
    _ = n := by rw [Module.finrank_pi_fintype, h1]; simp

/-- The section of `ℚ̄_ℓ,V` given by a constant function `a` is `a` times the unit section. -/
lemma adicConstantGlobalSection_algebraMap {V : Scheme.{u}} (a : PadicAlgCl l) :
    adicConstantGlobalSection (algebraMap (PadicAlgCl l) (PadicAlgCl.locallyFiniteFunctions l V) a)
      = (ULift.up a : ULift.{u + 1} (PadicAlgCl l)) •
        adicConstantGlobalSection (l := l) (V := V) 1 := by
  unfold adicConstantGlobalSection
  rw [← map_smul]
  congr 1
  exact congrArg ULift.up (Algebra.algebraMap_eq_smul_one a)

/-- The restriction to a point `s` of the unit section of `ℚ̄_ℓ,T`. -/
noncomputable def fibreUnitSection (s : Spec (.of Ω) ⟶ T) : (fibre l s).obj (unit l T) :=
  ((globalSectionsToUpperStar _ s).app (adicConstantSheaf l T)).hom (oneGlobalSection T)

/-- Through `s^* ℚ̄_ℓ,T ≅ ℚ̄_ℓ,Spec Ω`, the restriction to `s` of the section of a function `c`
is the constant `c(s)`. -/
lemma Γ_map_upperStarAdicConstantSheafHom_fibreUnitSection (s : Spec (.of Ω) ⟶ T)
    (c : PadicAlgCl.locallyFiniteFunctions l T) :
    ((Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l s)).hom
        (((globalSectionsToUpperStar _ s).app (adicConstantSheaf l T)).hom
          (adicConstantGlobalSection c)) =
      (ULift.up (c.1 (s.base (IsLocalRing.closedPoint Ω))) : ULift.{u + 1} (PadicAlgCl l)) •
        adicConstantGlobalSection (l := l) (V := Spec (.of Ω)) 1 := by
  rw [globalSectionsToUpperStar_adicConstantGlobalSection,
    PadicAlgCl.locallyFiniteFunctions_eq_algebraMap (T := Spec (.of Ω))
      (PadicAlgCl.locallyFiniteFunctionsComp l s.base.hom c) (IsLocalRing.closedPoint Ω),
    adicConstantGlobalSection_algebraMap]
  rfl

/-- **Evaluation at a point.** The fibre at `s` of an endomorphism `φ` of `ℚ̄_ℓ,T` is
multiplication by the value of its function at the image of `s`. -/
theorem fibre_map_unit_apply (s : Spec (.of Ω) ⟶ T) (φ : unit l T ⟶ unit l T)
    (z : (fibre l s).obj (unit l T)) :
    ((fibre l s).map φ).hom z =
      (ULift.up ((unitEndFun φ).1 (s.base (IsLocalRing.closedPoint Ω))) :
        ULift.{u + 1} (PadicAlgCl l)) • z := by
  let h := (Sheaf.Γ _ _).map (upperStarAdicConstantSheafHom l s)
  have hinj : Function.Injective h.hom :=
    (ModuleCat.mono_iff_injective h).1 inferInstance
  set x := fibreUnitSection (l := l) s
  have hx : h.hom x = adicConstantGlobalSection 1 := by
    have := Γ_map_upperStarAdicConstantSheafHom_fibreUnitSection (l := l) s 1
    rw [← oneGlobalSection_eq (l := l)] at this
    refine this.trans ?_
    rw [show (1 : PadicAlgCl.locallyFiniteFunctions l T).1 (s.base (IsLocalRing.closedPoint Ω))
      = 1 from rfl]
    exact one_smul _ _
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    have h00 : adicConstantGlobalSection (l := l) (V := Spec (.of Ω)) 0 = 0 := by
      unfold adicConstantGlobalSection
      exact map_zero _
    have := congrArg (fun c : PadicAlgCl.locallyFiniteFunctions l (Spec (.of Ω)) ↦
      c.1 (IsLocalRing.closedPoint Ω))
      (adicConstantGlobalSection_injective (hx.symm.trans h00.symm))
    exact one_ne_zero this
  have hφx : ((fibre l s).map φ).hom x =
      (ULift.up ((unitEndFun φ).1 (s.base (IsLocalRing.closedPoint Ω))) :
        ULift.{u + 1} (PadicAlgCl l)) • x := by
    apply hinj
    have n := congrArg (fun k ↦ k.hom (oneGlobalSection (l := l) T))
      ((globalSectionsToUpperStar _ s).naturality φ.hom)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Functor.comp_map] at n
    have e1 : ((fibre l s).map φ).hom x = ((globalSectionsToUpperStar _ s).app
        (adicConstantSheaf l T)).hom (adicConstantGlobalSection (unitEndFun φ)) := by
      rw [← Γ_map_hom_oneGlobalSection]
      exact n.symm
    rw [e1, Γ_map_upperStarAdicConstantSheafHom_fibreUnitSection, map_smul, hx]
  have hfin : Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((fibre l s).obj (unit l T))) = 1 := finrank_fibre_unit s
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := PadicAlgCl l)
    (V := (WeilCoefficients.toModuleCat l).obj ((fibre l s).obj (unit l T))) x hx0).1 hfin z
  change ((fibre l s).map φ).hom ((ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • x) =
    _ • ((ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • x)
  rw [map_smul, hφx, smul_comm]

variable (l) in
/-- The value at the closed point of a locally finite function on `Spec Ω`, as a linear map. -/
noncomputable def evalClosedPoint :
    (WeilCoefficients.toModuleCat l).obj (ModuleCat.of _
      (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l (Spec (.of Ω))))) →ₗ[PadicAlgCl l]
      PadicAlgCl l where
  toFun x := (ULift.down x).1 (IsLocalRing.closedPoint Ω)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (l) in
/-- The isomorphism of the fibre of `ℚ̄_ℓ,T` at `s` with the functions on the point `Spec Ω`,
through `s^* ℚ̄_ℓ,T ≅ ℚ̄_ℓ,Spec Ω`. -/
noncomputable def fibreUnitIso (s : Spec (.of Ω) ⟶ T) :
    (fibre l s).obj (unit l T) ≅ ModuleCat.of _
      (ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l (Spec (.of Ω)))) :=
  (Sheaf.Γ _ _).mapIso (asIso (upperStarAdicConstantSheafHom l s)) ≪≫
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology (Spec (.of Ω)))
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId _)).app
        (adicConstantSheaf l (Spec (.of Ω)))

variable (l) in
/-- The coordinate on the fibre of `ℚ̄_ℓ,T` at `s`: through `s^* ℚ̄_ℓ,T ≅ ℚ̄_ℓ,Spec Ω`, a section
is a function on the point `Spec Ω`, and the coordinate is its value. -/
noncomputable def fibreUnitCoord (s : Spec (.of Ω) ⟶ T) :
    (WeilCoefficients.toModuleCat l).obj ((fibre l s).obj (unit l T)) →ₗ[PadicAlgCl l]
      PadicAlgCl l :=
  (evalClosedPoint l).comp ((WeilCoefficients.toModuleCat l).map (fibreUnitIso l s).hom).hom

/-- The coordinate on the fibre of `ℚ̄_ℓ,T` is injective. -/
lemma fibreUnitCoord_injective (s : Spec (.of Ω) ⟶ T) :
    Function.Injective (fibreUnitCoord l s) := by
  intro x y h
  apply (WeilCoefficients.linearEquivOfIso (fibreUnitIso l s)).injective
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun p ↦ ?_))
  obtain rfl : p = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  exact h

/-- The coordinate of the fibre of an endomorphism `φ` of `ℚ̄_ℓ,T`: multiplication by the value
of the function of `φ` at the image of `s`. -/
lemma fibreUnitCoord_map (s : Spec (.of Ω) ⟶ T) (φ : unit l T ⟶ unit l T)
    (z : (fibre l s).obj (unit l T)) :
    fibreUnitCoord l s (((fibre l s).map φ).hom z) =
      (unitEndFun φ).1 (s.base (IsLocalRing.closedPoint Ω)) * fibreUnitCoord l s z := by
  rw [fibre_map_unit_apply]
  exact (fibreUnitCoord l s).map_smul _ z

variable (l) in
/-- The coordinates on the fibre of `ℚ̄_ℓ,Tᵃ` at `s`: the coordinates of the components. -/
noncomputable def fibreFreeCoord (s : Spec (.of Ω) ⟶ T) (a : ℕ) :
    (WeilCoefficients.toModuleCat l).obj ((fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T))
      →ₗ[PadicAlgCl l] (Fin a → PadicAlgCl l) :=
  LinearMap.pi fun j ↦ (fibreUnitCoord l s).comp
    ((WeilCoefficients.toModuleCat l).map ((fibre l s).map
      (biproduct.π (fun _ : Fin a ↦ unit l T) j))).hom

/-- The `j`-th coordinate is the coordinate of the `j`-th component. -/
lemma fibreFreeCoord_apply (s : Spec (.of Ω) ⟶ T) {a : ℕ}
    (y : (fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T)) (j : Fin a) :
    fibreFreeCoord l s a y j = fibreUnitCoord l s
      (((fibre l s).map (biproduct.π (fun _ : Fin a ↦ unit l T) j)).hom y) :=
  rfl

/-- An element of the fibre of `ℚ̄_ℓ,Tᵃ` is the sum of the fibres of the inclusions of its
components. -/
lemma fibre_free_eq_sum (s : Spec (.of Ω) ⟶ T) {a : ℕ}
    (y : (fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T)) :
    y = ∑ i, ((fibre l s).map (biproduct.ι (fun _ : Fin a ↦ unit l T) i)).hom
      (((fibre l s).map (biproduct.π (fun _ : Fin a ↦ unit l T) i)).hom y) := by
  have h := congrArg (fun k ↦ ((fibre l s).map k).hom y)
    (biproduct.total (f := fun _ : Fin a ↦ unit l T))
  simp only [Functor.map_sum, Functor.map_comp, ModuleCat.hom_sum, ModuleCat.hom_comp] at h
  rw [CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply, LinearMap.sum_apply] at h
  simpa only [LinearMap.comp_apply] using h.symm

/-- **The fibre of a morphism of finite free sheaves is its matrix at the point.** -/
lemma fibreFreeCoord_map (s : Spec (.of Ω) ⟶ T) {a b : ℕ}
    (ψ : (⨁ fun _ : Fin a ↦ unit l T) ⟶ ⨁ fun _ : Fin b ↦ unit l T)
    (y : (fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T)) :
    fibreFreeCoord l s b (((fibre l s).map ψ).hom y) =
      ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval
        (s.base (IsLocalRing.closedPoint Ω)))).mulVec (fibreFreeCoord l s a y) := by
  funext j
  rw [fibreFreeCoord_apply]
  conv_lhs => rw [fibre_free_eq_sum s y]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have key := fibreUnitCoord_map s (biproduct.ι (fun _ : Fin a ↦ unit l T) i ≫ ψ ≫
    biproduct.π (fun _ : Fin b ↦ unit l T) j)
    (((fibre l s).map (biproduct.π (fun _ : Fin a ↦ unit l T) i)).hom y)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key

/-- The coordinates on the fibre of `ℚ̄_ℓ,Tᵃ` are bijective. -/
lemma fibreFreeCoord_bijective (s : Spec (.of Ω) ⟶ T) (a : ℕ) :
    Function.Bijective (fibreFreeCoord l s a) := by
  have hinj : Function.Injective (fibreFreeCoord l s a) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 (i : Fin a) :
        ((fibre l s).map (biproduct.π (fun _ : Fin a ↦ unit l T) i)).hom y = 0 :=
      fibreUnitCoord_injective s ((congrFun hy i).trans (map_zero _).symm)
    rw [fibre_free_eq_sum s y]
    simp only [h0, map_zero, Finset.sum_const_zero]
  have : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T))) :=
    Module.Finite.of_injective _ hinj
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_fibre_free, Module.finrank_fin_fun]

/-- **Pointwise rank and fibres.** The rank of the fibre at `s` of a morphism of finite free
sheaves is the rank of its matrix of functions at the image of `s`. -/
theorem finrank_range_fibre_map (s : Spec (.of Ω) ⟶ T) {a b : ℕ}
    (ψ : (⨁ fun _ : Fin a ↦ unit l T) ⟶ ⨁ fun _ : Fin b ↦ unit l T) :
    Module.finrank (PadicAlgCl l)
        (LinearMap.range ((WeilCoefficients.toModuleCat l).map ((fibre l s).map ψ)).hom) =
      ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval
        (s.base (IsLocalRing.closedPoint Ω)))).rank := by
  let eb := LinearEquiv.ofBijective _ (fibreFreeCoord_bijective (l := l) s b)
  have hcomp : (fibreFreeCoord l s b).comp
      ((WeilCoefficients.toModuleCat l).map ((fibre l s).map ψ)).hom =
      ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval
        (s.base (IsLocalRing.closedPoint Ω)))).mulVecLin.comp (fibreFreeCoord l s a) :=
    LinearMap.ext fun y ↦ fibreFreeCoord_map s ψ y
  rw [Matrix.rank, ← (LinearEquiv.finrank_map_eq eb _), ← LinearMap.range_comp]
  erw [hcomp]
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.2 (fibreFreeCoord_bijective (l := l) s a).2)]

/-- The rank of a linear map is invariant under precomposition with a surjection and
postcomposition with an injection. -/
lemma _root_.LinearMap.finrank_range_comp_comp {K V₁ V₂ V₃ V₄ : Type*} [Field K]
    [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄] [Module K V₁]
    [Module K V₂] [Module K V₃] [Module K V₄] (f : V₂ →ₗ[K] V₃) (g : V₃ →ₗ[K] V₄)
    (hg : Function.Injective g) (h : V₁ →ₗ[K] V₂) (hh : Function.Surjective h) :
    Module.finrank K (LinearMap.range (g ∘ₗ f ∘ₗ h)) = Module.finrank K (LinearMap.range f) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hh)]
  exact (Submodule.equivMapOfInjective _ hg _).finrank_eq.symm

variable (l) in
/-- The fibre at `s` of a morphism of `ℓ`-adic sheaves, as a `ℚ̄_ℓ`-linear map. -/
noncomputable def fibreLin (s : Spec (.of Ω) ⟶ T) {M N : AdicSheaf l T} (φ : M ⟶ N) :
    (WeilCoefficients.toModuleCat l).obj ((fibre l s).obj M) →ₗ[PadicAlgCl l]
      (WeilCoefficients.toModuleCat l).obj ((fibre l s).obj N) :=
  ((WeilCoefficients.toModuleCat l).map ((fibre l s).map φ)).hom

/-- The fibre of a composite is the composite of the fibres. -/
lemma fibreLin_comp (s : Spec (.of Ω) ⟶ T) {M N P : AdicSheaf l T} (φ : M ⟶ N) (ψ : N ⟶ P) :
    fibreLin l s (φ ≫ ψ) = fibreLin l s ψ ∘ₗ fibreLin l s φ := by
  unfold fibreLin
  rw [Functor.map_comp, Functor.map_comp]
  rfl

variable (l) in
/-- The rank of the fibre at `s` of a morphism of `ℓ`-adic sheaves. -/
noncomputable def fibreRank (s : Spec (.of Ω) ⟶ T) {M N : AdicSheaf l T} (φ : M ⟶ N) : ℕ :=
  Module.finrank (PadicAlgCl l) (LinearMap.range (fibreLin l s φ))

/-- The rank of the fibre is invariant under composition with an isomorphism on the right and a
morphism with surjective fibre on the left. -/
lemma fibreRank_eq (s : Spec (.of Ω) ⟶ T) {M N M' N' : AdicSheaf l T} (φ : M ⟶ N)
    (α : M' ⟶ M) (β : N ≅ N') (hα : Function.Surjective (fibreLin l s α)) :
    fibreRank l s (α ≫ φ ≫ β.hom) = fibreRank l s φ := by
  unfold fibreRank
  rw [fibreLin_comp, fibreLin_comp, LinearMap.comp_assoc]
  exact LinearMap.finrank_range_comp_comp _ _
    (WeilCoefficients.linearEquivOfIso ((fibre l s).mapIso β)).injective _ hα

/-- The rank of the fibre is invariant under composition with isomorphisms. -/
lemma fibreRank_comp_iso (s : Spec (.of Ω) ⟶ T) {M N M' N' : AdicSheaf l T} (φ : M ⟶ N)
    (α : M' ≅ M) (β : N ≅ N') :
    fibreRank l s (α.hom ≫ φ ≫ β.hom) = fibreRank l s φ :=
  fibreRank_eq s φ α.hom β (WeilCoefficients.linearEquivOfIso ((fibre l s).mapIso α)).surjective

/-- At a geometric point, the rank of the fibre is invariant under precomposition with an
epimorphism. -/
lemma fibreRank_epi_comp [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) {M N M' : AdicSheaf l T}
    (φ : M ⟶ N) (π : M' ⟶ M) [Epi π] :
    fibreRank l s (π ≫ φ) = fibreRank l s φ := by
  have := fibreRank_eq s φ π (Iso.refl N)
    ((ModuleCat.epi_iff_surjective ((fibre l s).map π)).1 inferInstance)
  rwa [Iso.refl_hom, Category.comp_id] at this

/-- The rank of the fibre at `s` of a pullback along `p` is the rank of the fibre at `s ≫ p`. -/
lemma fibreRank_upperStar {T' : Scheme.{u}} (p : T' ⟶ T) (s : Spec (.of Ω) ⟶ T')
    {M N : AdicSheaf l T} (φ : M ⟶ N) :
    fibreRank l s ((p)^*ᵃ[l].map φ) = fibreRank l (s ≫ p) φ := by
  have h := (fibreUpperStarIso (l := l) p s).hom.naturality φ
  have h' : (fibre l s).map ((p)^*ᵃ[l].map φ) =
      (fibreUpperStarIso (l := l) p s).hom.app M ≫ (fibre l (s ≫ p)).map φ ≫
        (fibreUpperStarIso (l := l) p s).inv.app N := by
    rw [← reassoc_of% h]
    exact (Category.comp_id _).symm.trans
      (congrArg _ (Iso.hom_inv_id_app (fibreUpperStarIso (l := l) p s) N).symm)
  unfold fibreRank fibreLin
  rw [h', Functor.map_comp, Functor.map_comp]
  exact LinearMap.finrank_range_comp_comp _ _
    (WeilCoefficients.linearEquivOfIso ((fibreUpperStarIso (l := l) p s).app N).symm).injective _
    (WeilCoefficients.linearEquivOfIso ((fibreUpperStarIso (l := l) p s).app M)).surjective

/-- The pointwise rank of a morphism of finite free sheaves is the rank of its fibre at any
geometric point over the point. -/
lemma rank_unitMatrix_eq_fibreRank {a b : ℕ}
    (ψ : (⨁ fun _ : Fin a ↦ unit l T) ⟶ ⨁ fun _ : Fin b ↦ unit l T) (s : Spec (.of Ω) ⟶ T) :
    ((unitMatrix ψ).map (PadicAlgCl.locallyFiniteFunctionsEval
      (s.base (IsLocalRing.closedPoint Ω)))).rank = fibreRank l s ψ :=
  (finrank_range_fibre_map s ψ).symm

/-- **Lisse homology from locally constant ranks.** Let `S` be a short complex of finite free
`ℚ̄_ℓ,T`-modules whose two maps have locally constant pointwise ranks. Then the homology of `S`
is lisse: the cokernel `Q` of the first map is lisse, and after trivialising `Q` on a pro-étale
cover, the map `Q ⟶ X₃` induced by the second map has the same pointwise ranks as the second map
(compare the fibres at geometric points), so that its kernel, the homology, is lisse. -/
theorem isAdicLisseSheaf_homology_of_isLocallyConstant {a b c : ℕ}
    (S : ShortComplex (AdicSheaf l T)) (e₁ : S.X₁ ≅ ⨁ fun _ : Fin a ↦ unit l T)
    (e₂ : S.X₂ ≅ ⨁ fun _ : Fin b ↦ unit l T) (e₃ : S.X₃ ≅ ⨁ fun _ : Fin c ↦ unit l T)
    (hf : IsLocallyConstant fun t : T ↦
      ((unitMatrix (e₁.inv ≫ S.f ≫ e₂.hom)).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank)
    (hg : IsLocallyConstant fun t : T ↦
      ((unitMatrix (e₂.inv ≫ S.g ≫ e₃.hom)).map (PadicAlgCl.locallyFiniteFunctionsEval t)).rank) :
    IsAdicLisseSheaf S.homology := by
  have hQ : IsAdicLisseSheaf S.opcycles :=
    (isAdicLisseSheaf_kernel_of_eq_comp S.f (e₁.inv ≫ S.f ≫ e₂.hom) e₁.symm e₂ rfl
      (isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant _ hf)).2.of_iso
        S.opcyclesIsoCokernel.symm
  suffices h : IsAdicLisseSheaf (kernel S.fromOpcycles) from
    h.of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel _) S.homologyIsKernel)
  obtain ⟨R, hR, hRQ⟩ := hQ
  refine IsAdicLisseSheaf.of_presieve R hR fun V p hp ↦ ?_
  obtain ⟨n, ⟨eQ⟩⟩ := hRQ p hp
  let β : (p)^*ᵃ[l].obj S.X₃ ≅ ⨁ fun _ : Fin c ↦ unit l V :=
    (p)^*ᵃ[l].mapIso e₃ ≪≫ freeUpperStarIso l (Fin c) p
  have hrk : (fun v : V ↦ ((unitMatrix (eQ.symm.hom ≫ (p)^*ᵃ[l].map S.fromOpcycles ≫
      β.hom)).map (PadicAlgCl.locallyFiniteFunctionsEval v)).rank) =
      (fun t : T ↦ ((unitMatrix (e₂.inv ≫ S.g ≫ e₃.hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval t)).rank) ∘ p.base := by
    funext v
    obtain ⟨K, _, _, s, hs⟩ := Scheme.exists_isAlgClosed_apply_closedPoint_eq v
    have hsp : (s ≫ p).base (IsLocalRing.closedPoint _) = p.base v := by
      rw [Scheme.Hom.comp_apply, hs]
    rw [Function.comp_apply, ← hsp, ← hs, rank_unitMatrix_eq_fibreRank,
      rank_unitMatrix_eq_fibreRank, fibreRank_comp_iso, fibreRank_upperStar,
      ← fibreRank_epi_comp (s ≫ p) S.fromOpcycles S.pOpcycles, S.p_fromOpcycles,
      ← fibreRank_comp_iso (s ≫ p) S.g e₂.symm e₃]
    rfl
  have key := isAdicLisseSheaf_kernel_cokernel_of_isLocallyConstant
    (eQ.symm.hom ≫ (p)^*ᵃ[l].map S.fromOpcycles ≫ β.hom)
    (by rw [hrk]; exact hg.comp_continuous p.base.hom.continuous)
  exact (isAdicLisseSheaf_kernel_of_eq_comp ((p)^*ᵃ[l].map S.fromOpcycles) _ eQ.symm β rfl
    key).1.of_iso (PreservesKernel.iso _ _).symm

/-- The fibre of the zero morphism is zero. -/
lemma fibreLin_zero (s : Spec (.of Ω) ⟶ T) {M N : AdicSheaf l T} :
    fibreLin l s (0 : M ⟶ N) = 0 := by
  unfold fibreLin
  rw [Functor.map_zero, Functor.map_zero]
  rfl

/-- At a geometric point, the fibre of an exact sequence is exact. -/
lemma range_fibreLin_eq_ker [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    {S : ShortComplex (AdicSheaf l T)} (hS : S.Exact) :
    LinearMap.range (fibreLin l s S.f) = LinearMap.ker (fibreLin l s S.g) := by
  have hE := (ShortComplex.moduleCat_exact_iff (S.map (fibre l s))).1 (hS.map (fibre l s))
  refine le_antisymm ?_ fun y hy ↦ hE y hy
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← fibreLin_comp, S.zero, fibreLin_zero,
    LinearMap.zero_apply]

/-- The fibre of a finite free sheaf is finite-dimensional. -/
instance (s : Spec (.of Ω) ⟶ T) (a : ℕ) : FiniteDimensional (PadicAlgCl l)
    ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj (⨁ fun _ : Fin a ↦ unit l T))) :=
  Module.Finite.of_injective _ (fibreFreeCoord_bijective (l := l) s a).1

/-- **Dimension of the fibres of the homology.** At a geometric point, the fibre of the homology
of a short complex `S` with finite free middle term `ℚ̄_ℓ,Tᵇ` has dimension `b` minus the ranks
of the fibres of the two maps. -/
theorem finrank_fibre_homology [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T) {b : ℕ}
    (S : ShortComplex (AdicSheaf l T)) (e₂ : S.X₂ ≅ ⨁ fun _ : Fin b ↦ unit l T) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((fibre l s).obj S.homology)) + fibreRank l s S.f + fibreRank l s S.g = b := by
  have : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.X₂)) :=
    Module.Finite.equiv (WeilCoefficients.linearEquivOfIso ((fibre l s).mapIso e₂)).symm
  -- the cokernel sequence `X₁ ⟶ X₂ ⟶ Q ⟶ 0`
  let T₂ := ShortComplex.mk S.f S.pOpcycles S.f_pOpcycles
  have hT₂ : T₂.Exact := T₂.exact_of_g_is_cokernel S.opcyclesIsCokernel
  have hπ : Function.Surjective (fibreLin l s S.pOpcycles) :=
    (ModuleCat.epi_iff_surjective ((fibre l s).map S.pOpcycles)).1 inferInstance
  have hQ : FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.opcycles)) :=
    Module.Finite.of_surjective _ hπ
  have h₂ : Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.opcycles)) + fibreRank l s S.f =
      Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.X₂)) := by
    have h := LinearMap.finrank_range_add_finrank_ker (fibreLin l s S.pOpcycles)
    rw [LinearMap.range_eq_top.2 hπ, finrank_top, ← range_fibreLin_eq_ker s hT₂] at h
    exact h
  -- the kernel sequence `0 ⟶ H ⟶ Q ⟶ X₃`
  let T₁ := ShortComplex.mk S.homologyι S.fromOpcycles S.homologyι_comp_fromOpcycles
  have hT₁ : T₁.Exact := T₁.exact_of_f_is_kernel S.homologyIsKernel
  have hι : Function.Injective (fibreLin l s S.homologyι) :=
    (ModuleCat.mono_iff_injective ((fibre l s).map S.homologyι)).1 inferInstance
  have h₁ : fibreRank l s S.fromOpcycles + Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.homology)) =
      Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.opcycles)) := by
    have h := LinearMap.finrank_range_add_finrank_ker (fibreLin l s S.fromOpcycles)
    rw [← range_fibreLin_eq_ker s hT₁, LinearMap.finrank_range_of_inj hι] at h
    exact h
  have hg : fibreRank l s S.g = fibreRank l s S.fromOpcycles := by
    rw [← S.p_fromOpcycles, fibreRank_epi_comp]
  have hb : Module.finrank (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj S.X₂)) = b :=
    (WeilCoefficients.linearEquivOfIso ((fibre l s).mapIso e₂)).finrank_eq.trans
      (finrank_fibre_free s b)
  omega

end AdicSheaf

open AdicSheaf in
/-- **Perfect complexes have lisse cohomology on a locally Noetherian scheme.** Let `G n`,
`n ∈ ℤ`, be sheaves on a locally Noetherian scheme `Y` which, on the members `gᵢ : Uᵢ ⟶ Y` of a
pro-étale cover, are the homology sheaves of bounded above complexes `Cᵢ` of finite free
`ℚ̄_ℓ,Uᵢ`-modules. Then every `G n` is lisse.

The dimension of the fibre of `G n` at a geometric point over `u ∈ Uᵢ` is
`rank Cᵢⁿ - rank dⁿ⁻¹(u) - rank dⁿ(u)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.finrank_fibre_homology`),
so this function descends to `Y`. It is constant along specializations, the pointwise ranks of
the differentials being so and flat morphisms lifting generizations, hence locally constant.
Descending induction from the top degree shows that the pointwise ranks of the differentials are
locally constant, and the homology is lisse by
`AlgebraicGeometry.ProEtale.AdicSheaf.isAdicLisseSheaf_homology_of_isLocallyConstant`. -/
theorem isAdicLisseSheaf_of_isIso_homology_free {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (G : ℤ → AdicSheaf l Y) {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y)
    (hg : Presieve.ofArrows U g ∈ Scheme.proetalePrecoverage Y)
    (C : ∀ i, CochainComplex (AdicSheaf l (U i)) ℤ) (a : ι → ℤ → ℕ)
    (eC : ∀ i n, (C i).X n ≅ ⨁ fun _ : Fin (a i n) ↦ unit l (U i))
    (hb : ∀ i, ∃ N, ∀ n, N ≤ n → a i n = 0)
    (eG : ∀ i n, (g i)^*ᵃ[l].obj (G n) ≅ (C i).homology n) (n : ℤ) :
    IsAdicLisseSheaf (G n) := by
  classical
  have hgw (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hg (.mk i)
  -- pointwise ranks of the differentials
  let rk (i : ι) (p q : ℤ) (u : U i) : ℕ :=
    ((unitMatrix ((eC i p).inv ≫ (C i).d p q ≫ (eC i q).hom)).map
      (PadicAlgCl.locallyFiniteFunctionsEval u)).rank
  have hrk (i : ι) (p q : ℤ) {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ U i) :
      rk i p q (s.base (IsLocalRing.closedPoint K)) = fibreRank l s ((C i).d p q) := by
    simp only [rk]
    rw [rank_unitMatrix_eq_fibreRank]
    exact fibreRank_comp_iso s _ (eC i p).symm (eC i q)
  -- the dimension of the fibres of `G m`
  let D (m : ℤ) {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y) : ℕ :=
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj ((fibre l s).obj (G m)))
  have hD (i : ι) (m : ℤ) {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ U i) :
      D m (s ≫ g i) + rk i (m - 1) m (s.base (IsLocalRing.closedPoint K)) +
        rk i m (m + 1) (s.base (IsLocalRing.closedPoint K)) = a i m := by
    have h := finrank_fibre_homology s ((C i).sc m) (eC i m)
    have e : D m (s ≫ g i) = Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
        ((fibre l s).obj (((C i).sc m).homology))) :=
      (WeilCoefficients.linearEquivOfIso (((fibreUpperStarIso (g i) s).app (G m)).symm ≪≫
        (fibre l s).mapIso (eG i m))).finrank_eq
    rw [e, hrk, hrk, ← CochainComplex.prev ℤ m, ← CochainComplex.next ℤ m]
    exact h
  -- the pointwise ranks are constant along specializations
  have hspec (i : ι) (p q : ℤ) {u₀ u : U i} (hu : u₀ ⤳ u) : rk i p q u₀ = rk i p q u := by
    have : (unitMatrix ((eC i p).inv ≫ (C i).d p q ≫ (eC i q).hom)).map
        (PadicAlgCl.locallyFiniteFunctionsEval u₀) =
        (unitMatrix ((eC i p).inv ≫ (C i).d p q ≫ (eC i q).hom)).map
          (PadicAlgCl.locallyFiniteFunctionsEval u) := by
      ext x y
      exact (hu.map ((unitMatrix ((eC i p).inv ≫ (C i).d p q ≫ (eC i q).hom)) x y).1.continuous).eq
    simp only [rk, this]
  -- the dimension of the fibres of the homology, computed on the charts
  let hdim (i : ι) (m : ℤ) (u : U i) : ℕ := a i m - rk i (m - 1) m u - rk i m (m + 1) u
  have hdimD (i : ι) (m : ℤ) {K : Type u} [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ U i) :
      hdim i m (s.base (IsLocalRing.closedPoint K)) = D m (s ≫ g i) := by
    have h := hD i m s
    simp only [hdim]
    omega
  have hdesc (i j : ι) (m : ℤ) (u : U i) (u' : U j) (h : g i u = g j u') :
      hdim i m u = hdim j m u' := by
    obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback u u' h
    obtain ⟨K, _, _, s, hs⟩ := Scheme.exists_isAlgClosed_apply_closedPoint_eq w
    have h₁ : (s ≫ pullback.fst (g i) (g j)).base (IsLocalRing.closedPoint K) = u := by
      rw [Scheme.Hom.comp_apply, hs, hw]
    have h₂ : (s ≫ pullback.snd (g i) (g j)).base (IsLocalRing.closedPoint K) = u' := by
      rw [Scheme.Hom.comp_apply, hs, hw']
    have hc : (s ≫ pullback.fst (g i) (g j)) ≫ g i = (s ≫ pullback.snd (g i) (g j)) ≫ g j := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    rw [← h₁, ← h₂, hdimD, hdimD, hc]
  have hsurj : ∀ y, ∃ i, y ∈ Set.range (g i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1
      (Scheme.propQCPrecoverage_le_precoverage _ hg)).1
  choose kk vv hvv using hsurj
  let Hd (m : ℤ) (y : Y) : ℕ := hdim (kk y) m (vv y)
  have hHd (i : ι) (m : ℤ) (u : U i) : Hd m (g i u) = hdim i m u :=
    hdesc _ _ _ _ _ (hvv _)
  have hgen (m : ℤ) {η y : Y} (hηy : η ⤳ y) : Hd m η = Hd m y := by
    have hgm : GeneralizingMap (g (kk y)) := Flat.generalizingMap _
    obtain ⟨v₀, hv₀, hfv₀⟩ := hgm (show η ⤳ (g (kk y)) (vv y) by rw [hvv]; exact hηy)
    rw [← hfv₀, hHd]
    simp only [Hd, hdim, hspec _ _ _ hv₀]
  have hlc (m : ℤ) : IsLocallyConstant (Hd m) :=
    isLocallyConstant_of_specializes fun _ _ h ↦ hgen m h
  -- descending induction: the pointwise ranks of the differentials are locally constant
  have hrkc (i : ι) (m : ℤ) : IsLocallyConstant (rk i m (m + 1)) := by
    obtain ⟨N, hN⟩ := hb i
    have top (m : ℤ) (hm : N ≤ m) : IsLocallyConstant (rk i m (m + 1)) := by
      have h0 : rk i m (m + 1) = fun _ ↦ 0 := by
        funext u
        refine Nat.eq_zero_of_le_zero ((Matrix.rank_le_card_height _).trans ?_)
        simp [hN (m + 1) (by omega)]
      rw [h0]
      exact IsLocallyConstant.const 0
    have step (m : ℤ) (h : IsLocallyConstant (rk i m (m + 1))) :
        IsLocallyConstant (rk i (m - 1) (m - 1 + 1)) := by
      have hform : rk i (m - 1) (m - 1 + 1) =
          fun u ↦ a i m - Hd m (g i u) - rk i m (m + 1) u := by
        funext u
        obtain ⟨K, _, _, s, hs⟩ := Scheme.exists_isAlgClosed_apply_closedPoint_eq u
        have h' := hD i m s
        rw [hs] at h'
        rw [sub_add_cancel, hHd]
        simp only [hdim]
        omega
      rw [hform]
      exact ((hlc m).comp_continuous (g i).base.hom.continuous).comp₂ h
        fun x y ↦ a i m - x - y
    have down (k : ℕ) : IsLocallyConstant (rk i (N - k) (N - k + 1)) := by
      induction k with
      | zero => exact top _ (by omega)
      | succ k ih =>
        have := step _ ih
        rwa [show N - (k : ℤ) - 1 = N - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    rcases le_or_gt N m with hm | hm
    · exact top m hm
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = N - k := ⟨(N - m).toNat, by omega⟩
      rw [hk]
      exact down k
  -- the homology on the charts is lisse
  refine IsAdicLisseSheaf.of_presieve _ hg fun _ _ ⟨i⟩ ↦ ?_
  refine (isAdicLisseSheaf_homology_of_isLocallyConstant ((C i).sc n) (eC i _) (eC i n)
    (eC i _) ?_ ?_).of_iso (eG i n).symm
  · have hp (p : ℤ) (hp : p + 1 = n) : IsLocallyConstant (rk i p n) := by
      subst hp
      exact hrkc i p
    exact hp _ (by rw [CochainComplex.prev]; ring)
  · have hq (q : ℤ) (hq : n + 1 = q) : IsLocallyConstant (rk i n q) := by
      subst hq
      exact hrkc i n
    exact hq _ (CochainComplex.next ℤ n).symm

/-- **Locally perfect complexes have lisse cohomology** on a locally Noetherian scheme: if a
complex `K` of `ℓ`-adic sheaves on `Y` becomes, on the members of a pro-étale cover, isomorphic
in the derived category to bounded above complexes of finite free sheaves, then its cohomology
sheaves are lisse (`AlgebraicGeometry.ProEtale.isAdicLisseSheaf_of_isIso_homology_free`). -/
theorem isAdicLisseSheaf_homology_of_locally_free {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (K : DerivedCategory (AdicSheaf l Y)) {ι : Type*} {U : ι → Scheme.{u}} (g : ∀ i, U i ⟶ Y)
    (hg : Presieve.ofArrows U g ∈ Scheme.proetalePrecoverage Y)
    (C : ∀ i, CochainComplex (AdicSheaf l (U i)) ℤ) (a : ι → ℤ → ℕ)
    (eC : ∀ i n, (C i).X n ≅ ⨁ fun _ : Fin (a i n) ↦ AdicSheaf.unit l (U i))
    (hb : ∀ i, ∃ N, ∀ n, N ≤ n → a i n = 0)
    (eK : ∀ i, (g i)^*ᵃ[l].mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj (C i)) (n : ℤ) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ n).obj K) :=
  isAdicLisseSheaf_of_isIso_homology_free (fun m ↦ (DerivedCategory.homologyFunctor _ m).obj K)
    g hg C a eC hb (fun i m ↦ (((g i)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso m).app K) ≪≫
      (DerivedCategory.homologyFunctor _ m).mapIso (eK i) ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app (C i)) n

end AlgebraicGeometry.ProEtale
