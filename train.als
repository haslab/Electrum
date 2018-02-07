/**
An Alloy model of the Hybrid ERTMS/ETCS Level 3 Concept based on the Principles 
document at https://www.southampton.ac.uk/abz2018/information/case-study.page 
launched  as part of the ABZ 2018 call for case study contributions.

A technical report describing the Electurm version of this model and its development 
can be found at http://????.

This model is available at http://haslab.github.io/Electrum/ertms.als and its visualizer 
theme at http://haslab.github.io/Electrum/ertms_als.thm. A similar Electrum encoding can be 
found at haslab.github.io/Electrum/ertms.ele.

@author: Nuno Macedo
**/
open util/ordering[Time] as T
open util/ordering[VSS] as V
open util/ordering[TTD] as D

sig Time {}

enum State { Unknown, Free, Ambiguous, Occupied }

sig VSS {
	state 			: State one -> Time,	-- the current state of each VSS
	disconnect_ptimer	: set Time, 		-- whether the disconnect propagation timer has expired
	integrity_loss_ptimer	: set Time,			-- whether the integrity loss propagation timer has expired
	jumping			: Train lone -> Time 	-- jumping train detected by n02B imposes position update
}

fact jumpingTrain {
	jumping = { v:VSS,tr:Train,t:Time { 
		v.state.t = Occupied
		v.state.(t.prev) = Free
		parent[v] in occupied[t]
		n02B[t,v]
		tr.position_front.t = v }
	}
}

sig TTD {
	start 			: VSS,		-- first VSS of the TTD
	end 			: VSS,		-- last VSS of the TTD
	shadow_timer_A	: set Time,	-- whether the shadow timer A has expired
	shadow_timer_B	: set Time,	-- whether the shadow timer B has expired
	ghost_ptimer 	: set Time,	-- whether the ghost train propagation timer has expired
} {
	end.gte[start]
}

-- the VSSs that comprise a TTD
fun VSSs[t:TTD] : set VSS {
	t.start.*V/next & t.end.*(~V/next)
}

-- the parent TTD of a VSS
fun parent[v:VSS] : one TTD {
	max[(v.*V/prev).~start]
}

-- the concept of occupied TTD is instantaneous
-- NOTE: this isn't true in the spec, see scenario 5
fun occupied[t:Time] : set TTD {
	{ ttd : TTD | some VSSs[ttd] & Train.(position_rear+position_front).t }
}

-- correctly split the track into TDDs/VSSs
fact trackSections {
	all ttd:TTD-D/last | ttd.end.V/next = (ttd.D/next).start
	D/first.start = V/first
	D/last.end= V/last
}

sig Train {
	position_front 	: VSS one -> Time,		-- actual occupied front position, unknown to system
	position_rear 	: VSS one -> Time,		-- actual occupied rear position, unknown to system
	report_front 	: set Time,				-- last front position reported to the system
	report_rear 	: set Time,				-- last rear position reported to the system
	MA 			: VSS one -> Time,		-- current MAs assigned to the train
	connected		: set Time,				-- whether the train is connected
	mute_timer	: set Time,				-- whether the mute timer has expired for this train
	integrity_timer	: set Time,				-- whether the integrity timer has expired for this train
}

-- trains not reporting at a given instance
fun mute[t:Time] : set Train {
	Train-(report_rear+report_front).t
}

-- whether a train failed to report the rear position or is the result of a break up
-- NOTE: we use this to abstract the 3 conditions of n07B and n08A
fun disintegrated[t:Time] : set Train {
	report_front.t - report_rear.t 
}

fun MAs[t:Time,tr:Train] : set VSS {
	currentKnownRear[t,tr].*V/next & (tr.MA.t).*V/prev
}

-- trains with the TTD in its MA
fun MAs[t:Time,ttd:TTD] : set Train {
	{ tr:Train | some VSSs[ttd] & MAs[t,tr] }
}

-- trains with the VSS in its MA
fun MAs[t:Time,vss:VSS] : set Train {
	{ tr:Train | vss in MAs[t,tr] }
}

-- the last time the train reported before now
fun prevRep[t:Time,tr:Train] : one Time {
	max[t.^prev&tr.(report_front+report_rear)]
}

-- last positions reported
fun currentKnownLoc[t:Time,tr:Train] : set VSS {
	currentKnownFront[t,tr] + currentKnownRear[t,tr]
}

-- last front position reported
fun currentKnownFront[t:Time,tr:Train] : one VSS {
	some (jumping.t).tr => (jumping.t).tr else
	tr.position_front.(T/max[t.*prev&tr.report_front])
}

-- last rear position reported
fun currentKnownRear[t:Time,tr:Train] : one VSS {
	tr.position_rear.(T/max[t.*prev&tr.report_rear])
}

-- trains reported in a VSS
-- NOTE: cannot use jumping as this is used by n02B to create jumping; possibly raises issues
fun currentKnownTrain[t:Time,v: set VSS] : set Train {
	{ tr : Train | some tr.report_rear && tr.position_rear.(T/max[t.*prev&tr.report_rear]) in v }
	+
	{ tr : Train | some tr.report_front && tr.position_front.(T/max[t.*prev&tr.report_front]) in v }
}

-- trains reported in a TTD
fun positioned[t:Time,ttd:TTD] : set Train {
	{ tr:Train | some vss : VSSs[ttd] | tr in currentKnownTrain[t,vss] }
}

/**
Timers definition
**/

-- the mute timer for a train may expire if it is not reporting and always if not connected
-- forced to expire after one tick, it is enough for the scenarios of the spec
pred set_mute_timer[t:Time] {
	mute_timer.t in mute[t]
--	mute[t.prev] & mute[t] in mute_timer.t
}

-- the integrity timer for a train expire if it is "disintegrated" (clarify)
-- forced to expire after one tick, it is enough for the scenarios of the spec
pred set_integrity_timer[t:Time] {
	integrity_timer.t in disintegrated[t] 	
--	disintegrated[t] & disintegrated[t.prev] in integrity_timer.t
}

-- the shadow timers may expire if start conditions met previously and are preserved forever
-- cannot be forced to expire as this would break some scenarios
pred set_shadow_timer_A[t:Time] {
	shadow_timer_A.t in start_shadow_timer_A[t]
--	shadow_timer_A.(t.prev) in shadow_timer_A.t
}

fun start_shadow_timer_A[t:Time] : set TTD {
	{ ttd : TTD | some t': t.*T/prev {
			ttd in occupied[t'.prev]
			ttd not in occupied[t']
			ttd.end.state.(t'.prev) = Ambiguous
		}
	}
}

-- the shadow timers may expire if start conditions met previously and are preserved forever
-- cannot be forced to expire as this would break some scenarios
pred set_shadow_timer_B[t:Time] {
	shadow_timer_B.t in start_shadow_timer_B[t]
--	shadow_timer_B.(t.prev) in shadow_timer_B.t
}

pred auto_timer [t:Time] {
	start_shadow_timer_A[t] in shadow_timer_A.t
	start_shadow_timer_B[t] in shadow_timer_B.t
	start_ghost_ptimer[t] in ghost_ptimer.t
	start_integrity_loss_ptimer[t] in integrity_loss_ptimer.t
	mute[t] in mute_timer.t
	all vs:VSS | some (currentKnownTrain[t,vs])&mute_timer.t => vs in disconnect_ptimer.t
}

fun start_shadow_timer_B[t:Time] : set TTD {
	{ ttd : TTD | some t':t.*T/prev {
			ttd.end.state.t' = Unknown
			ttd.end.state.(t'.prev) = Ambiguous 
			some tr:positioned[t'.prev,ttd]-positioned[t',ttd] | tr not in disintegrated[t'.prev]
			-- NOTE: what about min-safe-rear-end?
		}
	}
}

-- the disconnected propagation timer may expire if the mute timer has expired
-- cannot be forced to expire as this would break some scenarios
pred set_disconnect_ptimer[t:Time] {
	all vs:VSS | vs in disconnect_ptimer.t => some (currentKnownTrain[t,vs])&mute_timer.t
--	all vs:VSS | (all t0:ts | some (currentKnownTrain[t,vs])&mute_timer.t0) => vs in disconnect_ptimer.t
}

-- the integrity propagation timer may expire if the integrity timer has expired
-- forced to expire after three tick, it is enough for the scenarios of the spec
pred set_integrity_loss_ptimer[t:Time] {
	integrity_loss_ptimer.t in start_integrity_loss_ptimer[t]
--	start_integrity_loss_ptimer[t] & start_integrity_loss_ptimer[t.prev] & start_integrity_loss_ptimer[t.prev.prev] & start_integrity_loss_ptimer[t.prev.prev.prev] in integrity_loss_ptimer.t
	integrity_loss_ptimer.(t.prev) in integrity_loss_ptimer.t
}

fun start_integrity_loss_ptimer[t:Time] : set VSS {
	{ vss : VSS | some t':t.*T/prev {
			vss in (state.(t'.prev)).Occupied
			some tr2 : currentKnownTrain[t',vss] |
				(tr2 in integrity_timer.t' && tr2 not in integrity_timer.(t'.T/prev)) 		
		}
	}
}

-- the ghost propagation timer may expire if start conditions met previously
-- NOTE: cannot be preserved forever as this would break S9; however, according to the spec it should
pred set_ghost_ptimer[t:Time] {
	ghost_ptimer.t in start_ghost_ptimer[t]
--	ghost_ptimer.(t.prev) in ghost_ptimer.t
}

fun start_ghost_ptimer[t:Time] : set TTD {
	{ ttd : TTD | some t':t.*T/prev {
			ttd in occupied[t']
			ttd not in occupied[t'.prev] && some t'.T/prev
			(no positioned[t',ttd] || no MAs[t',ttd])
		}
	}
}

-- set all timers
pred timers[t:Time] {
	set_mute_timer[t]
	set_integrity_timer[t]
	set_shadow_timer_A[t]
	set_shadow_timer_B[t]

	set_integrity_loss_ptimer[t]
	set_ghost_ptimer[t]
	set_disconnect_ptimer[t]
}

/**
System evolution
**/

-- sets the state of each VSS in the next state
pred states[t,t':Time,vss:VSS] {
	vss.state.t' = ( 
		n01[t,t',vss] 	=> 	Unknown else
		n02[t,t',vss] 	=> 	Occupied else 	-- priority over n03
		n03[t,t',vss] 	=> 	Ambiguous else
		n04[t,t',vss] 	=> 	Free else	 	-- priority over n05 and n12
		n12[t,t',vss] 	=> 	Occupied else	-- priority over n05
		n05[t,t',vss] 	=> 	Ambiguous else	
		n06[t,t',vss] 	=> 	Free else	 	
		n07[t,t',vss] 	=> 	Unknown else	-- priority over n08	 	
		n08[t,t',vss] 	=> 	Ambiguous else	
		n09[t,t',vss] 	=> 	Free else		-- priority over n10
		n10[t,t',vss] 	=> 	Unknown else	
		n11[t,t',vss] 	=> 	Occupied else	
						vss.state.t
	)
}

pred MAs[t,t':Time] {
	// if connected, assign MA to the max free vss in front
	all tr:connected.t | (tr.MA.t' = tr.MA.t || (currentKnownFront[t,tr].*next&tr.MA.t'.*V/prev).(state.t) = Free /*|| OSMA[t',tr]*/)
	// if disconnected, assign remove all MA
	all tr:(Train-connected.t)+mute_timer.t | (tr.MA.t' = tr.MA.t || tr.MA.t' = currentKnownFront[t,tr])
}

pred OSMA[t:Time,tr:Train] {
	currentKnownFront[t,tr] != V/last
	tr.MA.t = V/last
}

-- Free to Unknown
pred n01 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all n01*
	parent[v] in occupied[t']
	n01A[t',v] || n01B[t',v] || n01C[t',v] || n01D[t',v] || n01E[t',v] || n01F[t',v]
}

pred n01A [t:Time,v:VSS] {
	-- no FS MA issued or no train on TTD
	-- NOTE: the "no train on TTD" breaks the scenarios; also, 4.2.2 does not mention this
	no MAs[t,parent[v]] -- || no positioned[t,parent[v]]
}

pred n01B [t:Time,v:VSS] {
	-- VSS part of MA sent to a train for which mute timer expired
	some tr: MAs[t,v] & mute_timer.t {
		-- VSS is located after the VSS where train last reported
		v in currentKnownLoc[t.prev,tr].nexts
	}
}

pred n01C [t:Time,v:VSS] {
	some vss:disconnect_ptimer.t { 
		-- only free or unknown VSS between here and a VSS with disconnect propagation timer
		(vss.^next & v.^prev).(state.t) in Free+Unknown
		-- VSS on the same TTD as the one with timer
		parent[vss] = parent[v]
	}
}

pred n01D [t:Time,v:VSS] {
	some vss:disconnect_ptimer.t { 
		-- only free or unknown VSS between here and a VSS with disconnect propagation timer
		(vss.^next & v.^prev).(state.t) in Free+Unknown
		-- VSS not on the same TTD as the one with timer
		parent[vss] != parent[v]
		-- VSS not part of an MA
		no MAs[t,v]
	}
}

pred n01E [t:Time,v:VSS] {
	some vss:integrity_loss_ptimer.t { 
		-- only free or unknown VSS between here and a VSS with integrity loss propagation timer
		(vss.^next & v.^prev).(state.t) in Free+Unknown
		-- VSS on same TDD as the VSS for which integrity loss propagation timer
		parent[vss] = parent[v]
	}
}

pred n01F [t:Time,v:VSS] {
	some ttd:ghost_ptimer.t { 
		-- only free or unknown VSS between here and a VSS with ghost train propagation timer
		(ttd.end.nexts & v.prevs).(state.(t.prev)) in Free+Unknown
		-- VSS not on the same TTD as the one with timer
		ttd != parent[v]
	}
}

-- Free to Occupied
pred n02 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all n02*
	parent[v] in occupied[t']
	n02A[t',v] || n02B[t',v]
}

pred n02A [t:Time,v:VSS] {
	some tr: Train {
		-- there is a train on the VSS 
		v in currentKnownLoc[t,tr]
		-- the VSS of the front was occupied after the position report
		currentKnownFront[t.prev,tr].state.(prevRep[t,tr]) = Occupied
		-- current state of last reported VSS is not unknown
		Unknown != currentKnownFront[t.prev,tr].state.t
	}
}

pred n02B [t:Time,v:VSS] {
	-- TTD in rear is free
	parent[v].D/prev not in occupied[t]
	-- VSS is the first in TTD
	some v.~start
	-- there is a train on rear TTD
	some tr: Train {
		-- train is reported on last TTD
		tr in positioned[t,parent[v].D/prev]
		-- train is not reported on TTD
		tr not in positioned[t,parent[v]]
		-- the VSS of the front was occupied after the position report (*is this AFTER relevant?)
		currentKnownFront[t.prev,tr].state.(prevRep[t,tr]) = Occupied
		-- VSS part of MA
		tr in MAs[t,v]
	}
}

-- Free to Ambiguous
pred n03 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all n03*
	parent[v] in occupied[t']
	n03A[t',v] || n03B[t',v]
}

pred n03A [t:Time,v:VSS] {
	-- train reported on VSS
	some currentKnownTrain[t,v]
}

pred n03B [t:Time,v:VSS] {
	-- rear TTD free
	parent[v].D/prev not in occupied[t]
	-- there is a train in the previous TTD, not on this TTD, and v is part of its MA
	some tr:positioned[t,parent[v].D/prev]-positioned[t,parent[v]] | tr in MAs[t,v]
	-- first VSS of TTD
	v in TTD.start
}

-- Unknown to Free
pred n04 [t,t':Time,v:VSS] {
	v.state.t = Unknown
	n04A[t',v] || n04B[t',v] || n04C[t',v]
}

pred n04A [t:Time,v:VSS] {
	-- TDD free
	parent[v] not in occupied[t]
}

pred n04B [t:Time,v:VSS] {
	-- train reconnects for which VSS is in MA
	some tr:mute[t.prev]&MAs[t,v] {
		tr not in disintegrated[t]
		tr not in mute[t]
		some t0:t.prev.prevs | tr not in mute[t0] 
		some t.prev.prevs -- avoids SOM
		-- VSS is in advance of the VSS where the reconnected train is located
		v in (currentKnownFront[t,tr]).nexts
	}
}

pred n04C [t:Time,v:VSS] {
	-- train reconnects
	some tr:mute[t.prev] {
		tr not in disintegrated[t]
		tr not in mute[t]
		-- train data train length has not changed
		-- VSS is in advance of, or is, the VSS where the train was located when the connection was lost
		v in (currentKnownLoc[t.prev,tr]).*next -- guarantees that it was once connected
		-- VSS is in rear of the VSS where the reconnected train is located
		v in (currentKnownRear[t,tr]).prevs
		-- in rear of this VSS and subsequent VSS(s) that had become “unknown” because of the lost connection of this train is a “free” VSS on the same TTD as the train is located on
		let 	ts = t.^T/prev & T/max[(State-Unknown).(v.state)].^T/next, -- needed to identify reason for Unknown
			vs = (max[((state.(t.prev)).Free)&v.prevs]&VSSs[parent[v]]).nexts&(currentKnownRear[t,tr]).prevs |
			vs.state.(ts) = Unknown
	}
}

-- Unknown to Ambiguous
pred n05 [t,t':Time,v:VSS] {
	v.state.t = Unknown
	n05A[t',v] 
}

pred n05A [t:Time,v:VSS] {
	-- train on VSS
	some currentKnownTrain[t,v] & (report_front+report_rear).t -- problematic
}

-- Occupied to Free
pred n06 [t,t':Time,v:VSS] {
	v.state.t = Occupied
	n06A[t',v] || n06B[t',v]
}

pred n06A [t:Time,v:VSS] {
	-- TDD free
	parent[v] not in occupied[t]
}

pred n06B [t:Time,v:VSS] {
	-- a train was on the VSS and was reported leaving
	some tr:Train {
		-- integer train
		tr not in disintegrated[t]
		tr not in mute[t]
		v not in currentKnownLoc[t,tr]
		v in currentKnownLoc[t.prev,tr]
	}
}

-- Occupied to Unknown
pred n07 [t,t':Time,v:VSS] {
	v.state.t = Occupied
	n07A[t',v] || n07B[t',v]
}

pred n07A [t:Time,v:VSS] {
	-- train with mute timer expired or EoM
	-- train on VSS
	some tr:currentKnownTrain[t,v] | tr in mute_timer.t || eom[t.prev,t,tr] 
}

pred n07B [t:Time,v:VSS] {
	-- a train was on the VSS and was reported leaving
	some tr:Train {
		v not in currentKnownLoc[t,tr]
		v in currentKnownLoc[t.prev,tr]
		(tr in integrity_timer.t && tr not in integrity_timer.(t.T/prev))
	}
}

-- Occupied to Ambiguous
pred n08 [t,t':Time,v:VSS] {
	v.state.t = Occupied
	n08A[t',v] || n08B[t',v] || n08C[t',v]
}

pred n08A [t:Time,v:VSS] {
	-- train on VSS
	some tr: currentKnownTrain[t,v] |
		(tr in integrity_timer.t && tr not in integrity_timer.(t.T/prev))
}

pred n08B [t:Time,v:VSS] {
	-- train on VSS
	some currentKnownTrain[t,v]
	-- rear VSS is unknown
	v.prev.state.t = Unknown
}

pred n08C [t:Time,v:VSS] {
	-- trains on VSS
	some disj tr1,tr2: currentKnownTrain[t,v] | not integral[t,tr1,tr2]
}

-- Ambiguous to Free
pred n09 [t,t':Time,v:VSS] {
	v.state.t = Ambiguous
	n09A[t',v] || n09B[t',v]
}

pred n09A [t:Time,v:VSS] {
	-- TDD free
	parent[v] not in occupied[t]
}

pred n09B [t:Time,v:VSS] {
	-- a train was on the VSS and was reported leaving
	some tr:Train {
		-- integer train
		tr not in disintegrated[t]
		v not in currentKnownLoc[t,tr]
		v in currentKnownLoc[t.prev,tr]
		-- no shadow timer
		parent[v] not in shadow_timer_A.t		
		parent[v] in start_shadow_timer_A[t]
	}
}

-- Ambiguous to Unknown
pred n10 [t,t':Time,v:VSS] {
	v.state.t = Ambiguous
	n10A[t',v] || n10B[t',v]
}

pred n10A [t:Time,v:VSS] {
	-- all trains reported leaving
	some currentKnownTrain[t.prev,v]
	all tr:Train {
		(tr in currentKnownTrain[t.prev,v] && tr in connected.t) => 
			(tr not in currentKnownTrain[t,v])
	}
}

pred n10B [t:Time,v:VSS] {
	-- train on VSS and mute timer expired
	some currentKnownTrain[t,v] & (mute_timer.t + (Train - connected.t))
}

-- Ambiguous to Occupied
pred n11 [t,t':Time,v:VSS] {
	v.state.t = Ambiguous
	n11A[t',v] || n11B[t',v]
}

pred n11A [t:Time,v:VSS] {
	some tr: currentKnownTrain[t,v] {
		tr not in disintegrated[t]
		-- train left the previous TTD
		no currentKnownLoc[t,tr] & VSSs[parent[v].D/prev]
	}
	-- shadow train timer A of the TTD in rear was not exprired
	parent[v].D/prev not in shadow_timer_A.t
	parent[v].D/prev in start_shadow_timer_A[t]

	-- NOTE: what about min-safe-rear-end?
}

pred n11B [t:Time,v:VSS] {
	-- TTD in rear is free
	parent[v].D/prev not in occupied[t]
	-- integer train located on the VSS reported to have left the TTD in rear
	some tr: currentKnownTrain[t,v] {
		-- integer train
		tr not in disintegrated[t]
		tr not in mute[t]
		some currentKnownLoc[t.prev,tr] & VSSs[parent[v].D/prev]
	}
	-- the “shadow train timer B” of the TTD in rear for this direction was not expired at the moment of the time stamp in the position report
	parent[v].D/prev not in shadow_timer_B.t
	parent[v].D/prev in start_shadow_timer_B[t]
}

-- Unknown to Occupied
pred n12 [t,t':Time,v:VSS] {
	v.state.t = Unknown
	n12A[t',v] || n12B[t',v]
}

pred n12A [t:Time,v:VSS] {
	-- train located on the VSS
	some tr: currentKnownTrain[t,v] {
		-- reconnects within same session
		tr in mute[t.prev]
		tr not in mute[t]
		-- integer train
		tr not in disintegrated[t]
		-- In rear of this VSS and subsequent VSS(s) that had become “unknown” because of the lost connection of this train is a “free” VSS on an “occupied” TTD
		let 	ts = t.^T/prev & T/max[(State-Unknown).(v.state)].^T/next, -- needed to identify reason for Unknown
			vs = (max[((state.(t.prev)).Free)&v.prevs]&VSSs[occupied[t]]).nexts&(currentKnownRear[t,tr]).prevs |
			vs.state.(ts) = Unknown
	}
}

pred n12B [t:Time,v:VSS] {
	parent[v] in occupied[t]
	-- train located on the VSS
	some tr: currentKnownTrain[t,v] {
		-- the VSS of the front was occupied after the position report
		(currentKnownFront[t.prev,tr]).state.(prevRep[t,tr]) = Occupied
		-- the train is not re-connecting, i.e. the mute timer was not expired
		tr not in mute_timer.(t.prev)
		-- current state of last reported VSS is not unknown
		Unknown != (currentKnownFront[t.prev,tr]).state.(t.prev)		
	}
}


run n01A 	{some t:Time,v:VSS | n01[t,t.next,v] && n01A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n01B 	{some t:Time,v:VSS | n01[t,t.next,v] && n01B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n01C 	{some t:Time,v:VSS | n01[t,t.next,v] && n01C[t.next,v]} 	for 8 but 3 TTD, 2 Train expect 1
run n01D 	{some t:Time,v:VSS | n01[t,t.next,v] && n01D[t.next,v]} 	for 8 but 3 TTD, 2 Train expect 1
run n01E 	{some t:Time,v:VSS | n01[t,t.next,v] && n01E[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n01F 	{some t:Time,v:VSS | n01[t,t.next,v] && n01F[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n02A 	{some t:Time,v:VSS | n02[t,t.next,v] && n02A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n02B 	{some t:Time,v:VSS | n02[t,t.next,v] && n02B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n03A 	{some t:Time,v:VSS | n03[t,t.next,v] && n03A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n03B 	{some t:Time,v:VSS | n03[t,t.next,v] && n03B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n04A 	{some t:Time,v:VSS | n04[t,t.next,v] && n04A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n04B 	{some t:Time,v:VSS | n04[t,t.next,v] && n04B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n04C 	{some t:Time,v:VSS | n04[t,t.next,v] && n04C[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n05A 	{some t:Time,v:VSS | n05[t,t.next,v] && n05A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n06A 	{some t:Time,v:VSS | n06[t,t.next,v] && n06A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n06B 	{some t:Time,v:VSS | n06[t,t.next,v] && n06B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n07A 	{some t:Time,v:VSS | n07[t,t.next,v] && n07A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n07B 	{some t:Time,v:VSS | n07[t,t.next,v] && n07B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n08A 	{some t:Time,v:VSS | n08[t,t.next,v] && n08A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n08B 	{some t:Time,v:VSS | n08[t,t.next,v] && n08B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n08C 	{some t:Time,v:VSS | n08[t,t.next,v] && n08C[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n09A 	{some t:Time,v:VSS | n09[t,t.next,v] && n09A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n09B 	{some t:Time,v:VSS | n09[t,t.next,v] && n09B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n10A 	{some t:Time,v:VSS | n10[t,t.next,v] && n10A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n10B 	{some t:Time,v:VSS | n10[t,t.next,v] && n10B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n11A 	{some t:Time,v:VSS | n11[t,t.next,v] && n11A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n11B 	{some t:Time,v:VSS | n11[t,t.next,v] && n11B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n12A 	{some t:Time,v:VSS | n12[t,t.next,v] && n12A[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1
run n12B 	{some t:Time,v:VSS | n12[t,t.next,v] && n12B[t.next,v]} 	for 6 but 3 TTD, 2 Train expect 1


/**
Train movement
**/

/*
a train moves and reports to the trackside
the report is safe: if anything is reported, it is correct
the report may become empty, abstracting disconnected trains
or it may report the front position but not the rear, abstracting non-integer trains
*/
pred move [t,t':Time,tr:Train] {
	-- actual movement
	-- front does not move or goes to next
	tr.position_front.t' in tr.position_front.t + (tr.position_front.t).V/next 
	-- rear stays between the new front and the old rear, but moving a single VSS
	tr.position_rear.t' in tr.position_front.t' + (tr.position_front.t').prev
	tr.position_rear.t' in tr.position_rear.t + (tr.position_rear.t).V/next

-- 	the train can move to positions without MA, see 1.2.3.3

	-- reported position
	{
		t in tr.connected
		t' in tr.report_rear => t' in tr.report_front
	} || {
		t' not in tr.report_front
		t' not in tr.report_rear
	}
	t in tr.connected iff t' in tr.connected

	t in tr.connected => tr.position_front.t' in MAs[t',tr]
}

pred som[t,t':Time,tr:Train] {
	tr not in connected.t
	connected.t' = connected.t + tr
	
	report_rear.t' = report_rear.t + tr
	report_front.t' = report_front.t + tr
	position_front.t' = position_front.t
	position_rear.t' = position_rear.t
}

pred eom[t,t':Time,tr:Train] {
	tr in connected.t
	connected.t' = connected.t - tr

	report_rear.t' = report_rear.t - tr
	report_front.t' = report_front.t - tr
	position_front.t' = position_front.t
	position_rear.t' = position_rear.t
}

pred integral[t:Time,tr,tr':Train] {
	all t0 : t.*T/prev {
		tr'.MA.t0 = tr.MA.t0
		tr'.position_front.t0 = tr.position_front.t0
		tr'.position_rear.t0 = tr.position_rear.t0
		t0 in tr'.report_front iff t0 in tr.report_front
		t0 in tr'.report_rear iff t0 in tr.report_rear
	}
}

pred split [t,t':Time,tr,tr':Train] {
	tr != tr'
	integral[t,tr,tr']
	t' not in tr'.(report_rear+report_front)
	tr.position_rear.t' in tr.position_front.t + tr.position_rear.t
	tr'.position_front.t' = tr'.position_front.t
	tr'.position_rear.t' = tr'.position_rear.t
	position_rear.t' - (tr+tr') -> VSS = position_rear.t - (tr+tr') -> VSS
	position_front.t' - tr' -> VSS = position_front.t - tr' -> VSS
	report_rear.t' = report_rear.t - (tr' + tr)
	report_front.t' = report_front.t - tr'
	t in tr'.connected
	t' not in tr'.connected
}

fact trace {
	all t:Time,t':t.next {
		timers[t]
		MAs[t,t']
		all v:VSS | states[t,t',v]
		(all tr:Train | move[t,t',tr]) || (some tr,tr':Train | split[t,t',tr,tr'] || som[t,t',tr] || eom[t,t',tr]) 
	}
	timers[last]
}

/**
Scenarios
Note: cannot start from all unknown, as this will not lead
to the scenarios without a new dummy initial TTD (see
scenario 4 on start of mission).
**/

pred S1 {

	no integrity_timer + mute_timer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, t3 = t2.next, 
		t4 = t3.next, t5 = t4.next, t6 = t5.next, t7 = t6.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some tr:Train {
		// initial state
		v11.state.t0 = Occupied
		v11.nexts.state.t0 = Free

		tr.report_front = Time
		tr.report_rear = t0+t2+t4+t6+t7

		tr.(position_front+position_rear).t0 = v11
		tr.(position_front+position_rear).t1 = v12
		tr.(position_front+position_rear).t2 = v12
		tr.(position_front+position_rear).t3 = v21
		tr.(position_front+position_rear).t4 = v21
		tr.(position_front+position_rear).t5 = v22
		tr.(position_front+position_rear).t6 = v23
		tr.(position_front+position_rear).t7 = v31

		// final state
		v31.state.t7 = Occupied
		(VSS-v31).state.t7 = Free
	}
	}
}


pred S2 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + disconnect_ptimer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, t3 = t2.next, 
		t4 = t3.next, t5 = t4.next, t6 = t5.next, t7 = t6.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next,
		v32 = v31.next, v33 = v32.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some disj tr1,tr2:Train {
		// initial state
		v11.state.t0 = Free
		v12.state.t0 = Occupied
		v12.nexts.state.t0 = Free

		tr1.report_rear = Time - (t1+t6)
		tr1.report_front = Time - t6
		tr2.report_rear = t0
		tr2.report_front = t0
		t0 = tr2.connected
		Time = tr1.connected

		no tr1.mute_timer
		no mute_timer.t1
		no integrity_loss_ptimer.(t4.prevs)
		v12 = integrity_loss_ptimer.t4

		split[t0,t1,tr1,tr2]

		tr1.(position_front+position_rear).t0 = v12
		tr1.(position_front+position_rear).t2 = v21
		tr1.(position_front+position_rear).t3 = v22
		tr1.(position_front+position_rear).t4 = v23
		tr1.(position_front+position_rear).t5 = v31+v23
		tr1.(position_front+position_rear).t6 = v31
		tr1.(position_front+position_rear).t7 = v31

		tr2.(position_front+position_rear).t0 = v12
		tr2.(position_front+position_rear).t7 = v12

		tr2.MA.(t1.nexts) = v12

		// final state
--		(v11+v12).state.t7 = Unknown
		v31.state.t7 = Occupied
		(v21+v22+v23+v32+v33).state.t7 = Free
	}
	}
}


-- NOTES: at t5, VSS5 changes from Free to Unknown due to n01A, but in the scenario
--		n01A is not triggered, why? changed n01A according to 4.2.2
--		at t7, VSS6 changes from Unknown to Occupied by n11B due to the shadow 
--		timer A; yet in the scenario the timer is not started because "because the virtual 
--		rear end is more than the shadow timer B travel distance from the TTD20 
--		border"; how to model this?
pred S3 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + disconnect_ptimer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, t3 = t2.next, 
		t4 = t3.next, t5 = t4.next, t6 = t5.next, t7 = t6.next, 
		t8 = t7.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next,
		v32 = v31.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some disj tr1,tr2:Train {
		// initial state
		v11.state.t0 = Free
		v12.state.t0 = Occupied
		v12.nexts.state.t0 = Free

		tr1.report_front = Time-t5
		tr1.report_rear = Time-(t1+t5)
		tr2.report_rear = t0
		tr2.report_front = t0

		no tr1.mute_timer
		no mute_timer.t1
		some integrity_loss_ptimer.t1
		some integrity_timer.t1

		split[t0,t1,tr1,tr2]

		tr1.(position_front+position_rear).t0 = v12
		tr1.(position_front+position_rear).t2 = v21
		tr1.(position_front+position_rear).t3 = v22
		tr1.(position_front+position_rear).t4 = v23
		tr1.(position_front+position_rear).t5 = v31
		tr1.(position_front+position_rear).t6 = (v31+v32)
		tr1.(position_front+position_rear).t7 = v32
		tr1.(position_front+position_rear).t8 = v32

		tr2.(position_front+position_rear).t0 = v12
		tr2.(position_front+position_rear).t2 = v12
		tr2.(position_front+position_rear).t3 = v12
		tr2.(position_front+position_rear).t4 = v21
		tr2.(position_front+position_rear).t5 = v22
		tr2.(position_front+position_rear).t6 = v23
		tr2.(position_front+position_rear).t7 = v31
		tr2.(position_front+position_rear).t8 = v31

		tr2.MA.(t1.nexts) = v12

		// final state
		v31.state.t8 = Unknown
		v32.state.t8 = Ambiguous
		(VSS-(v31+v32)).state.t8 = Free
	}
	}
}


-- NOTES:	at t3, VSS2 changes to Ambiguous before going to Occupied; 
--		yet in the scenario it goes directly from Free to Occupied; I think
--		this is simplified at the scenario
pred S4 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + integrity_timer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
		t3 = t2.next, t4 = t3.next, t5 = t4.next, 
		t6 = t5.next, t7 = t6.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next,
		v32 = v31.next, v33 = v32.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some tr:Train {
		// initial state
		(v11+v12).state.t0 = Unknown
		v12.nexts.state.t0 = Free
		
		tr.connected = Time - (t0+t6+t7)

		t1+t2+t3+t4+t5 = tr.report_rear
		t1+t2+t3+t4+t5 = tr.report_front

		tr.(position_front+position_rear).t0 = v11
		tr.(position_front+position_rear).t1 = v11
		tr.(position_front+position_rear).t2 = v12
		tr.(position_front+position_rear).t3 = v21
		tr.(position_front+position_rear).t4 = v21
		tr.(position_front+position_rear).t5 = v22
		tr.(position_front+position_rear).t6 = v22
		tr.(position_front+position_rear).t7 = v22

		no disconnect_ptimer.t6
		some disconnect_ptimer.t7
		no mute_timer.t6
		some mute_timer.t7 

		// final state
--		(v21+v22+v23).state.t7 = Unknown
		(v11+v12+v31+v32+v33).state.t7 = Free
	}
	}
}


-- NOTES:	at t6 all VSSs change automatically to Free; in the scenario
--		a delay on the TTD detection system is applied, which is not
--		implemented in this model
-- due to the absence of delay on TTD, VSS turns to Occupied through 11A rather than 11B
pred S5 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + disconnect_ptimer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
		t3 = t2.next, t4 = t3.next, t5 = t4.next, 
		t6 = t5.next, t7 = t6.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next,
		v32 = v31.next, v33 = v32.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some disj tr1,tr2:Train {
		// initial state
		v11.state.t0 = Free
		v12.state.t0 = Occupied
		v12.nexts.state.t0 = Free

		tr1.report_front = Time
		Time-(t1+t2) in tr1.report_rear
		tr2.report_front = t0
		tr2.report_rear = t0

		split[t0,t1,tr1,tr2]

		t4.*next = VSS.integrity_loss_ptimer

		tr1.(position_front+position_rear).t0 = v12
		tr1.(position_front+position_rear).t2 = v21
		tr1.(position_front+position_rear).t3 = v22
		tr1.(position_front+position_rear).t4 = v23
		tr1.(position_front+position_rear).t5 = v23+v31
		tr1.(position_front+position_rear).t6 = v31
		tr1.(position_front+position_rear).t7 = v31

		tr2.(position_front+position_rear).t0 = v12
		tr2.(position_front+position_rear).t7 = v12

		tr2.MA.(t1.nexts) = v12

		// final state
		(v11+v12).state.t7 = Unknown
		v31.state.t7 = Occupied
		(v21+v22+v23+v32+v33).state.t7 = Free
	}
	}
}

-- NOTES: at t4, VSS4 changes from Free to Unknown due to n01A, but in the scenario
--		n01A is not triggered, why? changed n01A according to 4.2.2
-- NOTES: at t8, VSS5 changes to Ambiguous before going to Occupied; 
--		yet in the scenario it goes directly from Free to Occupied;
--		this is simplified at the scenario
pred S6 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + integrity_loss_ptimer + integrity_timer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
		t3 = t2.next, t4 = t3.next, t5 = t4.next, 
		t6 = t5.next, t7 = t6.next, t8 = t7.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some disj tr1:Train {
		// initial state
		v11.state.t0 = Free
		v12.state.t0 = Occupied
		v12.nexts.state.t0 = Free
	
		t0+t5+t6+t7+t8 = tr1.report_rear
		t0+t5+t6+t7+t8 = tr1.report_front
		t0+t5+t6+t7+t8 = tr1.connected

		tr1.(position_front+position_rear).t0 = v12
		tr1.(position_front+position_rear).t1 = v12
		tr1.(position_front+position_rear).t2 = v12
		tr1.(position_front+position_rear).t3 = v21
		tr1.(position_front+position_rear).t4 = v22
		tr1.(position_front+position_rear).t5 = v22
		tr1.(position_front+position_rear).t6 = v23
		tr1.(position_front+position_rear).t7 = v31

		no mute_timer.(t0+t1)
		tr1 in mute_timer.t2

		t1 not in univ.disconnect_ptimer
		t2 not in univ.disconnect_ptimer
		t3 not in univ.disconnect_ptimer
		t4 in univ.disconnect_ptimer

		tr1.MA.(t0+t1+t2+t3+t4+t5) = v22
		tr1.MA.(t6.*next) = V/last

		// final state
		v31.state.t8 = Occupied
		(VSS-v31).state.t8 = Free
	}
	}
}


pred S7 {

	no ghost_ptimer + shadow_timer_A + shadow_timer_B + integrity_loss_ptimer + disconnect_ptimer + integrity_timer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
			t3 = t2.next, t4 = t3.next, t5 = t4.next, 
			t6 = t5.next, t7 = t6.next, t8 = t7.next,
			v11 = V/first, v12 = v11.next, v21 = v12.next,
			v22 = v21.next, v23 = v22.next, v31 = v23.next,
			v32 = v31.next {
	v12 in parent[first].end
	v31 in parent[last].start

	some tr1:Train {
		// initial state
		(v11+v12).state.t0 = Free
		v21.state.t0 = Occupied
		v21.nexts.state.t0 = Free

		tr1.connected = t0+t1+t2+t6.*next
		tr1.report_front = t0+t1+t2+t6.*next
		tr1.report_rear = t0+t1+t2+t6.*next

		tr1.(position_front+position_rear).t0 = v21
		tr1.(position_front+position_rear).t1 = v22
		tr1.(position_front+position_rear).t2 = v22
		tr1.(position_front+position_rear).t3 = v22
		tr1.(position_front+position_rear).t4 = v23
		tr1.(position_front+position_rear).t5 = v23+v31
		tr1.(position_front+position_rear).t6 = v23+v31
		tr1.(position_front+position_rear).t7 = v31
		tr1.(position_front+position_rear).t8 = v32

		tr1.mute_timer = t4+t5

		tr1.MA.Time = v32

		// final state
		v32.state.t8 = Occupied
		(VSS-v32).state.t8 = Free
	}
	}
}


/*
	at t5, the state of VSS2 in the scenario changes directly from Unknown to Occupied,
	but here it goes first into Ambiguous; yet, in the description n11A is mentioned, so
	it is probably a simplification in the scenario
*/
pred S8 {
--	no ghost_ptimer + shadow_timer_A + shadow_timer_B + integrity_loss_ptimer + disconnect_ptimer + mute_timer + integrity_timer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
		t3 = t2.next, t4 = t3.next, t5 = t4.next, 
		t6 = t5.next, t7 = t6.next, t8 = t7.next,
		t9 = t8.next, t10 = t9.next,
		v11 = V/first, v12 = v11.next, v21 = v12.next,
		v22 = v21.next, v23 = v22.next, v31 = v23.next,
		v32 = v31.next, v33 = v32.next, v4 = v33.next {
	v12 in parent[v11].end
	v31 in parent[v33].start
	v4 in TTD.start

	some disj tr1,tr2:Train {
		// initial state		
		v12.nexts.state.t0 = Free
		(v11+v12).state.t0 = Occupied

		t0+t1+t2+t3+t4+t5+t6+t7+t8+t9+t10 in tr1.report_rear
		t0+t1+t2+t3+t4+t5+t6+t7+t8+t9+t10 in tr1.report_front
		Time-t10 = tr2.report_front
		Time-t10 = tr2.report_rear

		tr1.(position_front+position_rear).(t0+t1) = v12
		tr1.(position_front+position_rear).t2 = v21
		tr1.(position_front+position_rear).t3 = v22
		tr1.(position_front+position_rear).t4 = v23
		tr1.(position_front+position_rear).(t5+t6) = v31
		tr1.(position_front+position_rear).t7 = v32
		tr1.(position_front+position_rear).t8 = v33
		tr1.(position_front+position_rear).(t9+t10) = v4
		
		tr2.(position_front+position_rear).t0 = v11
		tr2.(position_front+position_rear).t1 = v11+v12
		tr2.(position_front+position_rear).(t2+t3+t4) = v12
		tr2.(position_front+position_rear).(t5+t6) = v21
		tr2.(position_front+position_rear).(t7+t8) = v22
		tr2.(position_front+position_rear).t9 = v23
		tr2.(position_front+position_rear).t10 = v31
	
		// final state
		(v31).state.t10 = Occupied
		(VSS-(v31+v4)).state.t10 = Free
	}
	}
}


/*
	This scenario requires that the front report be processed before the rear report!
	This isn't modeled, must be unfolded into two states.
*/
pred S9 {
	no shadow_timer_A + shadow_timer_B + integrity_loss_ptimer + disconnect_ptimer

	let	t0 = T/first, t1 = t0.next, t2 = t1.next, 
			t3 = t2.next, t4 = t3.next, t5 = t4.next, 
			t6 = t5.next, t7 = t6.next, t8 = t7.next,
			t9 = t8.next,
			v0 = V/first, v11 = v0.next, v12 = v11.next, v21 = v12.next,
			v22 = v21.next, v23 = v22.next, v31 = v23.next,
			v32 = v31.next, v33 = v32.next {
	v12 in parent[v12].end
	v31 in parent[v33].start
	v0 in TTD.end

	some disj tr1,tr2:Train {
		// initial state
		v23.state.t0 = Occupied
		v0.state.t0 = Unknown
		(VSS-(v23+v0)).state.t0 = Free

		tr1.connected = Time
		tr2.connected = t4.nexts
		t0+t1+t2+t3+t4 in tr1.report_front
		t0+t1+t2+t3+t4+t6+t7+t8+t9 in tr1.report_rear

		integrity_timer = tr2 -> t9

		tr1.(position_front+position_rear).(t0+t1+t2) = v23
		tr1.position_front.t3 = v31
		tr1.position_rear.t3 = v23
		tr1.position_front.t4 = v32
		tr1.position_rear.t4 = v31
		tr1.(position_front+position_rear).t6 = v32
		tr1.(position_front+position_rear).t7 = v32 + v33
		tr1.(position_front+position_rear).t9 = v33

		tr2.(position_front+position_rear).t0 = v0
		tr2.(position_front+position_rear).(t1+t2) = v11
		tr2.(position_front+position_rear).(t3+t4+t5+t6) = v12
		tr2.(position_front+position_rear).(t7+t8) = v21
		tr2.(position_front+position_rear).t9 = v22
	
		no ghost_ptimer.t1
		some ghost_ptimer.t2
		no ghost_ptimer.t7 -- wrong!
	
		// final state
		v21.state.t9 = Unknown
		v22.state.t9 = Ambiguous
		v33.state.t9 = Occupied
		(VSS-(v21+v22+v33)).state.t9 = Free
	}
	}
}

run S1 for exactly 1 Train, exactly 3 TTD, exactly 8 VSS, 8 Time expect 1
run S2 for exactly 2 Train, exactly 3 TTD, exactly 8 VSS, 8 Time expect 1
run S3 for exactly 2 Train, exactly 3 TTD, exactly 8 VSS, 9 Time expect 1
run S4 for exactly 1 Train, exactly 3 TTD, exactly 8 VSS, 8 Time expect 1
run S5 for exactly 2 Train, exactly 3 TTD, exactly 8 VSS, 8 Time expect 1
run S6 for exactly 1 Train, exactly 3 TTD, exactly 8 VSS, 9 Time expect 1
run S7 for exactly 1 Train, exactly 3 TTD, exactly 8 VSS, 9 Time expect 1
run S8 for exactly 2 Train, exactly 4 TTD, exactly 9 VSS, 11 Time expect 1
run S9 for exactly 2 Train, exactly 4 TTD, exactly 9 VSS, 10 Time expect 1

/**
Verification
**/
pred init_allOK[t:Time] {
	some Train
	no mute_timer.t + integrity_timer.t + shadow_timer_A.t + shadow_timer_B.t + integrity_loss_ptimer.t + disconnect_ptimer.t
	Train = connected.t & report_rear.t & report_front.t
	all tr:Train | tr.position_front.t = tr.position_rear.t && tr.(position_rear+position_front).t.(state.t) = Occupied
	(VSS - (Train.(position_rear+position_front).t)).state.t = Free
	all tr:Train | tr.MA.t in tr.position_front.t.*V/next &&
		all tr' : Train-tr | no MAs[t,tr] & MAs[t,tr']
}

-- if no train goes mute or disintegrated, then free is always correctly assigned (no train)
assert trains_ok_free_ok {
	(init_allOK[T/first] && all t:Time | no mute[t] && no disintegrated[t]) =>
		all t:Time | (VSS-Train.(position_front+position_rear).t).state.t = Free
}

-- if no train goes mute or disintegrated, then occupied is always correctly assigned (exactly one train)
assert trains_ok_occupied_ok {
	(init_allOK[T/first] && all t:Time | no mute[t] && no disintegrated[t]) =>
		all t:Time | Train.(position_front+position_rear).t.state.t = Occupied
}

-- if no train goes mute or disintegrated, then no unknown or ambiguous states are assigned
assert trains_ok_states_ok {
	(init_allOK[T/first] && all t:Time | no mute[t] && no disintegrated[t]) =>
		VSS.state.(T/first.nexts) in Free + Occupied
}

-- if all timers are automatic and the trains move within the MAs, then occupied is always correctly assigned (exactly one train)
assert timers_auto_occupied_ok {
	(init_allOK[T/first] && all t:Time,tr:Train | auto_timer[t] && tr.position_front.t in MAs[t,tr]) =>
		all t:Time-last, v:VSS| (v.state.t in Occupied) =>
			lone (position_front.t + position_rear.t).v
}

-- if all timers are automatic and the trains move within the MAs, then no free is incorrectly assigned (some train)
assert timers_auto_free_ok {
	(init_allOK[T/first] && all t:Time,tr:Train | auto_timer[t] && tr.position_front.t in MAs[t,tr]) =>
		all t:Time-last, tr:Train | (tr.position_front.t).state.t != Free
}

-- 8 VSS, 4 TTD, 2 Train, 10 Time: 2mins
-- 8 VSS, 4 TTD, 2 Train, 15 Time: 5mins
-- 10 VSS, 5 TTD, 3 Train, 15 Time: 25mins
-- 10 VSS, 4 TTD, 3 Train, 15 Time: 40mins
-- 10 VSS, 4 TTD, 2 Train, 8 Time: 1min
-- 10 VSS, 4 TTD, 3 Train, 12 Time: 10mins
check timers_auto_free_ok 		for 10 VSS, 4 TTD, 3 Train, 15 Time expect 0
-- 8 VSS, 4 TTD, 2 Train, 10 Time: 2mins
-- 8 VSS, 4 TTD, 2 Train, 15 Time: 4mins
-- 10 VSS, 5 TTD, 3 Train, 15 Time: 60mins
-- 10 VSS, 4 TTD, 3 Train, 15 Time: 40mins
-- 10 VSS, 4 TTD, 2 Train, 8 Time: 1min
-- 10 VSS, 4 TTD, 3 Train, 12 Time: 15mins
check timers_auto_occupied_ok	for 10 VSS, 4 TTD, 3 Train, 15 Time expect 0
-- 8 VSS, 4 TTD, 2 Train, 10 Time: 10mins
-- 8 VSS, 4 TTD, 2 Train, 15 Time: 40mins
-- 10 VSS, 5 TTD, 3 Train, 15 Time: ????
-- 10 VSS, 4 TTD, 2 Train, 8 Time: 15mins
check trains_ok_states_ok		for 10 VSS, 4 TTD, 3 Train, 12 Time expect 0
-- 8 VSS, 4 TTD, 2 Train, 10 Time: 15mins
-- 8 VSS, 4 TTD, 2 Train, 15 Time: 60mins
-- 10 VSS, 5 TTD, 3 Train, 15 Time: ????
-- 10 VSS, 4 TTD, 2 Train, 8 Time: ????
check trains_ok_occupied_ok 	for 10 VSS, 4 TTD, 3 Train, 12 Time expect 0
-- 8 VSS, 4 TTD, 2 Train, 10 Time: 20mins
-- 8 VSS, 4 TTD, 2 Train, 15 Time: 60mins
-- 10 VSS, 5 TTD, 3 Train, 15 Time: ????
-- 10 VSS, 4 TTD, 2 Train, 8 Time: ????
check trains_ok_free_ok 		for 10 VSS, 4 TTD, 3 Train, 12 Time expect 0

/**
Visualization
**/

fun _occupied : Time -> TTD {
	{t:Time, ttd : TTD| ttd in occupied[t] }
}
fun _occupied : Time -> VSS {
	{t:Time, vss : VSS| Occupied = vss.state.t }
}
fun _unknown: Time -> VSS {
	{t:Time, vss : VSS| Unknown = vss.state.t }
}
fun _free : Time -> VSS {
	{t:Time, vss : VSS| Free = vss.state.t }
}
fun _ambiguous : Time -> VSS {
	{t:Time, vss : VSS| Ambiguous = vss.state.t }
}
fun _VSSs : Time -> TTD -> VSS {
	Time -> { t:TTD, v: t.start.*V/next & t.end.*(~V/next) }
}

fun _Arear : Train -> Time { report_rear } // needed due to alphabetical order


