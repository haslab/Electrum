/**
An Alloy model of the Hybrid ERTMS/ETCS Level 3 Concept (HL3) based on the "Principles"
document at https://www.southampton.ac.uk/abz2018/information/case-study.page 
launched  as part of the ABZ 2018 call for case study contributions.

A technical report describing the corresponding Electrum model and its development can 
be found at http://haslab.github.io/Electrum/ertms.pdf.

This model is available at http://haslab.github.io/Electrum/ertms.als and its visualizer theme 
at http://haslab.github.io/Electrum/ertms_als.thm. A similar Electrum encoding can be found at 
http://haslab.github.io/Electrum/ertms.ele.

@author: Nuno Macedo
**/
open util/ordering[Time] as T
open util/ordering[VSS] as V
open util/ordering[TTD] as D

sig Time {}

/**
Structural components of the HL3 model, including the track configurations and train state, 
and the communication between on-board and the trackside systems.
**/

-- the states that can be assigned to each VSS
enum State { Unknown, Free, Ambiguous, Occupied }

-- virtual sub-sections of the track, totally ordered
sig VSS {
	state 			: State one -> Time,	-- the current state of the VSS
	disconnect_ptimer	: set Time, 			-- whether the disconnect propagation timer of the VSS has expired
	integrity_loss_ptimer	: set Time,				-- whether the integrity loss propagation timer of the VSS has expired
	jumping			: Train lone -> Time 	-- jumping trains detected by #2B
}

-- trackside train detection sections, totally ordered
sig TTD {
	start 			: VSS,		-- first VSS of the TTD
	end 			: VSS,		-- last VSS of the TTD
	shadow_timer_A	: set Time,	-- whether the shadow timer A of the TTD has expired
	shadow_timer_B	: set Time,	-- whether the shadow timer B of the TTD has expired
	ghost_ptimer 	: set Time,	-- whether the ghost train propagation timer of the TTD has expired
} { end.gte[start] }

-- all VSSs that comprise a TTD
fun VSSs[t:TTD] : set VSS {
	t.start.*V/next & t.end.*(~V/next)
}

-- the parent TTD of a VSS
fun parent[v:VSS] : one TTD {
	max[(v.*V/prev).~start]
}

-- the concept of occupied TTD is instantaneous
-- NOTE: this is not assumed in the HL3, affects Scenario 5
fun occupied[t:Time] : set TTD {
	{ ttd : TTD | some VSSs[ttd] & Train.(pos_rear+pos_front).t }
}

-- enforce total partition of the track into TDDs/VSSs
fact trackSections {
	all ttd:TTD-D/last | ttd.end.V/next = (ttd.D/next).start
	D/first.start = V/first
	D/last.end= V/last
}

-- available trains, always positioned in the track
sig Train {
	pos_front 		: VSS one -> Time,	-- actual front end position, unknown to trackside
	pos_rear 		: VSS one -> Time,	-- actual rear end position, unknown to trackside
	connected		: set Time,			-- whether the train is connected to the trackside
	report_front	: set Time,			-- whether the train reported PTD front information
	report_rear 	: set Time,			-- whether the train reported PTD rear information
	MA 			: VSS one -> Time,	-- current MA assigned to the train by the trackside
	mute_timer	: set Time,			-- whether the mute timer of the train has expired
	integrity_timer	: set Time,			-- whether the integrity timer of the train has expired
}

-- trains not reporting at a given instant
fun mute[t:Time] : set Train {
	Train-(report_rear+report_front).t
}

-- whether a train failed to report the rear position or is the result of a break up
-- NOTE: this abstracts the 3 conditions of #7B and #8A and the ghost propagation timer
fun disintegrated[t:Time] : set Train {
	report_front.t - report_rear.t 
}

-- all VSSs comprising the MA of a train
fun MAs[t:Time,tr:Train] : set VSS {
	knownRear[t,tr].*V/next & (tr.MA.t).*V/prev
}

-- all trains whose MA includes the TTD
fun MAs[t:Time,ttd:TTD] : set Train {
	{ tr:Train | some VSSs[ttd] & MAs[t,tr] }
}

-- all trains whose MA includes the VSS
fun MAs[t:Time,vss:VSS] : set Train {
	{ tr:Train | vss in MAs[t,tr] }
}

-- the previous time the train reported
fun prevRep[t:Time,tr:Train] : one Time {
	max[t.^prev&tr.(report_front+report_rear)]
}

-- last reported position of the train
fun knownLoc[t:Time,tr:Train] : set VSS {
	knownFront[t,tr] + knownRear[t,tr]
}

-- last reported front end position of the train
fun knownFront[t:Time,tr:Train] : one VSS {
	some (jumping.t).tr => (jumping.t).tr else
	tr.pos_front.(T/max[t.*prev&tr.report_front])
}

-- last reported rear end position of the train
fun knownRear[t:Time,tr:Train] : one VSS {
	tr.pos_rear.(T/max[t.*prev&tr.report_rear])
}

-- trains whose last reported position was the VSS
fun knownTrain[t:Time,v: set VSS] : set Train {
	{ tr : Train | some tr.report_rear && tr.pos_rear.(T/max[t.*prev&tr.report_rear]) in v }
	+
	{ tr : Train | some tr.report_front && tr.pos_front.(T/max[t.*prev&tr.report_front]) in v }
}

-- trains reported in a TTD
fun positioned[t:Time,ttd:TTD] : set Train {
	{ tr:Train | some vss : VSSs[ttd] | tr in knownTrain[t,vss] }
}

-- forces the detection of jumping trains due to #2B
fact jumpingTrain {
	jumping = { v:VSS,tr:Train,t:Time { 
		v.state.t = Occupied
		v.state.(t.prev) = Free
		parent[v] in occupied[t]
		n02B[t,v]
		tr.pos_front.t = v }
	}
}

/**
Timers start and stop events definition. No particular duration imposed, only possibility 
of expiration is encoded. Expired timers do not remain so indefinitely as this would 
break, e.g., Scenario 9.
**/

-- the mute timer for a train may expire if it is not reporting
pred set_mute_timer[t:Time] {
	mute_timer.t in mute[t]
}

-- the integrity timer for a train expire if it is disintegrated
pred set_integrity_timer[t:Time] {
	integrity_timer.t in disintegrated[t] 	
}

-- the shadow timer A of a TTD may expire if start conditions were once met
pred set_shadow_timer_A[t:Time] {
	shadow_timer_A.t in start_shadow_timer_A[t]
}

-- shadow timer A start event conditions
fun start_shadow_timer_A[t:Time] : set TTD {
	{ ttd : TTD | some t': t.*T/prev {
			ttd in occupied[t'.prev]
			ttd not in occupied[t']
			ttd.end.state.(t'.prev) = Ambiguous
		}
	}
}

-- the shadow timer B of a TTD may expire if start conditions were once met
pred set_shadow_timer_B[t:Time] {
	shadow_timer_B.t in start_shadow_timer_B[t]
}

-- shadow timer B start event conditions
fun start_shadow_timer_B[t:Time] : set TTD {
	{ ttd : TTD | some t':t.*T/prev {
			ttd.end.state.t' = Unknown
			ttd.end.state.(t'.prev) = Ambiguous 
			some tr:positioned[t'.prev,ttd]-positioned[t',ttd] | tr not in disintegrated[t'.prev]
			-- NOTE: ignores min-safe-rear-end
		}
	}
}

-- the disconnect propagation timer for a VSS may expire if a train last reported
-- in it has the mute timer expired
pred set_disconnect_ptimer[t:Time] {
	all vs:VSS | vs in disconnect_ptimer.t => some (knownTrain[t,vs])&mute_timer.t
--	all vs:VSS | (all t0:ts | some (knownTrain[t,vs])&mute_timer.t0) => vs in disconnect_ptimer.t
}

-- the integrity loss propagation timer of a train may expire if start conditions were 
-- once met
pred set_integrity_loss_ptimer[t:Time] {
	integrity_loss_ptimer.t in start_integrity_loss_ptimer[t]
}

-- integrity loss propagation timer start event conditions
fun start_integrity_loss_ptimer[t:Time] : set VSS {
	{ vss : VSS | some t':t.*T/prev {
			vss in (state.(t'.prev)).Occupied
			some tr2 : knownTrain[t',vss] |
				(tr2 in integrity_timer.t' && tr2 not in integrity_timer.(t'.T/prev)) 		
		}
	}
}

-- the ghost propagation timer of a TTD may expire if start conditions were once met
pred set_ghost_ptimer[t:Time] {
	ghost_ptimer.t in start_ghost_ptimer[t]
}

-- ghost propagation timer start event conditions
fun start_ghost_ptimer[t:Time] : set TTD {
	{ ttd : TTD | some t':t.*T/prev {
			ttd in occupied[t']
			ttd not in occupied[t'.prev] && some t'.T/prev
			(no positioned[t',ttd] || no MAs[t',ttd])
		}
	}
}

-- enforce all timer expiration conditions
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
Trackside system evolution, including the VSS state machine and the assignment of MAs.
**/

-- encodes the VSS state machine according to the defined priorities
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

-- VSS state transition #1 from Free to Unknown
pred n01 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all #1
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
		v in knownLoc[t.prev,tr].nexts
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

-- VSS state transition #2 from Free to Occupied
pred n02 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all #2
	parent[v] in occupied[t']
	n02A[t',v] || n02B[t',v]
}

pred n02A [t:Time,v:VSS] {
	some tr: Train {
		-- there is a train on the VSS 
		v in knownLoc[t,tr]
		-- the VSS of the front was occupied after the position report
		knownFront[t.prev,tr].state.(prevRep[t,tr]) = Occupied
		-- current state of last reported VSS is not unknown
		Unknown != knownFront[t.prev,tr].state.t
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
		-- the VSS of the front was occupied after the position report
		knownFront[t.prev,tr].state.(prevRep[t,tr]) = Occupied
		-- VSS part of MA
		tr in MAs[t,v]
	}
}

-- VSS state transition #3 from Free to Ambiguous
pred n03 [t,t':Time,v:VSS] {
	v.state.t = Free
	-- TTD is occupied, common to all #3
	parent[v] in occupied[t']
	n03A[t',v] || n03B[t',v]
}

pred n03A [t:Time,v:VSS] {
	-- train reported on VSS
	some knownTrain[t,v]
}

pred n03B [t:Time,v:VSS] {
	-- rear TTD free
	parent[v].D/prev not in occupied[t]
	-- there is a train in the previous TTD, not on this TTD, and v is part of its MA
	some tr:positioned[t,parent[v].D/prev]-positioned[t,parent[v]] | tr in MAs[t,v]
	-- first VSS of TTD
	v in TTD.start
}

-- VSS state transition #4 from Unknown to Free
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
		some t.prev.prevs
		-- VSS is in advance of the VSS where the reconnected train is located
		v in (knownFront[t,tr]).nexts
	}
}

pred n04C [t:Time,v:VSS] {
	-- train reconnects
	some tr:mute[t.prev] {
		tr not in disintegrated[t]
		tr not in mute[t]
		-- train data train length has not changed
		-- VSS is in advance of, or is, the VSS where the train was located when the connection was lost
		v in (knownLoc[t.prev,tr]).*next -- guarantees that it was once connected
		-- VSS is in rear of the VSS where the reconnected train is located
		v in (knownRear[t,tr]).prevs
		-- in rear of this VSS and subsequent VSS(s) that had become “unknown” because of the lost 
		-- connection of this train is a “free” VSS on the same TTD as the train is located on
		let 	ts = t.^T/prev & T/max[(State-Unknown).(v.state)].^T/next,
			vs = (max[((state.(t.prev)).Free)&v.prevs]&VSSs[parent[v]]).nexts&(knownRear[t,tr]).prevs |
			vs.state.(ts) = Unknown
	}
}

-- VSS state transition #5 from Unknown to Ambiguous
pred n05 [t,t':Time,v:VSS] {
	v.state.t = Unknown
	n05A[t',v] 
}

pred n05A [t:Time,v:VSS] {
	-- train on VSS
	some knownTrain[t,v] & (report_front+report_rear).t -- NOTE: not the standard notion of located
}

-- VSS state transition #6 from Occupied to Free
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
		v not in knownLoc[t,tr]
		v in knownLoc[t.prev,tr]
	}
}

-- VSS state transition #7 from Occupied to Unknown
pred n07 [t,t':Time,v:VSS] {
	v.state.t = Occupied
	n07A[t',v] || n07B[t',v]
}

pred n07A [t:Time,v:VSS] {
	-- train with mute timer expired or EoM
	-- train on VSS
	some tr:knownTrain[t,v] | tr in mute_timer.t || eom[t.prev,t,tr] 
}

pred n07B [t:Time,v:VSS] {
	-- a train was on the VSS and was reported leaving
	some tr:Train {
		v not in knownLoc[t,tr]
		v in knownLoc[t.prev,tr]
		(tr in integrity_timer.t && tr not in integrity_timer.(t.T/prev))
	}
}

-- VSS state transition #8 from Occupied to Ambiguous
pred n08 [t,t':Time,v:VSS] {
	v.state.t = Occupied
	n08A[t',v] || n08B[t',v] || n08C[t',v]
}

pred n08A [t:Time,v:VSS] {
	-- train on VSS
	some tr: knownTrain[t,v] |
		(tr in integrity_timer.t && tr not in integrity_timer.(t.T/prev))
}

pred n08B [t:Time,v:VSS] {
	-- train on VSS
	some knownTrain[t,v]
	-- rear VSS is unknown
	v.prev.state.t = Unknown
}

pred n08C [t:Time,v:VSS] {
	-- trains on VSS
	some disj tr1,tr2: knownTrain[t,v] | not integral[t,tr1,tr2]
}

-- VSS state transition #9 from Ambiguous to Free
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
		v not in knownLoc[t,tr]
		v in knownLoc[t.prev,tr]
		-- no shadow timer
		parent[v] not in shadow_timer_A.t		
		parent[v] in start_shadow_timer_A[t]
	}
}

-- VSS state transition #10 from Ambiguous to Unknown
pred n10 [t,t':Time,v:VSS] {
	v.state.t = Ambiguous
	n10A[t',v] || n10B[t',v]
}

pred n10A [t:Time,v:VSS] {
	-- all trains reported leaving
	some knownTrain[t.prev,v]
	all tr:Train {
		(tr in knownTrain[t.prev,v] && tr in connected.t) => 
			(tr not in knownTrain[t,v])
	}
}

pred n10B [t:Time,v:VSS] {
	-- train on VSS and mute timer expired
	some knownTrain[t,v] & (mute_timer.t + (Train - connected.t))
}

-- VSS state transition #11 from Ambiguous to Occupied
pred n11 [t,t':Time,v:VSS] {
	v.state.t = Ambiguous
	n11A[t',v] || n11B[t',v]
}

pred n11A [t:Time,v:VSS] {
	some tr: knownTrain[t,v] {
		tr not in disintegrated[t]
		-- train left the previous TTD
		no knownLoc[t,tr] & VSSs[parent[v].D/prev]
	}
	-- shadow train timer A of the TTD in rear was not exprired
	parent[v].D/prev not in shadow_timer_A.t
	parent[v].D/prev in start_shadow_timer_A[t]

	-- NOTE: ignores about min-safe-rear-end
}

pred n11B [t:Time,v:VSS] {
	-- TTD in rear is free
	parent[v].D/prev not in occupied[t]
	-- integer train located on the VSS reported to have left the TTD in rear
	some tr: knownTrain[t,v] {
		-- integer train
		tr not in disintegrated[t]
		tr not in mute[t]
		some knownLoc[t.prev,tr] & VSSs[parent[v].D/prev]
	}
	-- the “shadow train timer B” of the TTD in rear for this direction was not expired at the moment 
	-- of the time stamp in the position report
	parent[v].D/prev not in shadow_timer_B.t
	parent[v].D/prev in start_shadow_timer_B[t]
}

-- VSS state transition #12 from Unknown to Occupied
pred n12 [t,t':Time,v:VSS] {
	v.state.t = Unknown
	n12A[t',v] || n12B[t',v]
}

pred n12A [t:Time,v:VSS] {
	-- train located on the VSS
	some tr: knownTrain[t,v] {
		-- reconnects within same session
		tr in mute[t.prev]
		tr not in mute[t]
		-- integer train
		tr not in disintegrated[t]
		-- In rear of this VSS and subsequent VSS(s) that had become “unknown” because of the lost 
		-- connection of this train is a “free” VSS on an “occupied” TTD
		let 	ts = t.^T/prev & T/max[(State-Unknown).(v.state)].^T/next, -- needed to identify reason for Unknown
			vs = (max[((state.(t.prev)).Free)&v.prevs]&VSSs[occupied[t]]).nexts&(knownRear[t,tr]).prevs |
			vs.state.(ts) = Unknown
	}
}

pred n12B [t:Time,v:VSS] {
	parent[v] in occupied[t]
	-- train located on the VSS
	some tr: knownTrain[t,v] {
		-- the VSS of the front was occupied after the position report
		(knownFront[t.prev,tr]).state.(prevRep[t,tr]) = Occupied
		-- the train is not re-connecting, i.e. the mute timer was not expired
		tr not in mute_timer.(t.prev)
		-- current state of last reported VSS is not unknown
		Unknown != (knownFront[t.prev,tr]).state.(t.prev)		
	}
}

-- updates the MAs assigned to a train according to VSS state and PTD information
-- NOTE: note defined in the HL3, loose reasonable assumptions
pred MAs[t,t':Time] {
	-- if a train is connected, do nothing, assign MA to a free VSS in front or assign OS MA
	all tr:connected.t | (tr.MA.t' = tr.MA.t || (knownFront[t,tr].*next&tr.MA.t'.*V/prev).(state.t) = Free || OSMA[t',tr])
	-- if a train is connected, do nothing or remove MA (assign to current known position)
	all tr:(Train-connected.t)+mute_timer.t | (tr.MA.t' = tr.MA.t || tr.MA.t' = knownFront[t,tr])
}

-- assigns OS MA to a train by allowing free movement up to the last VSS
pred OSMA[t:Time,tr:Train] {
	knownFront[t,tr] != V/last
	tr.MA.t = V/last
}


/**
Train movement and PTD reporting.
**/

-- encodes valid train movement and the reporting of PTD information.
-- each train may move one VSS at a time, and the front and rear end must not be more
-- than a VSS away.
-- may not report PTD information at all; may report only front information, meaning
-- lost integrity.
-- if connected, obbeys the MA.
pred move [t,t':Time,tr:Train] {
	-- possible effective train movement
	tr.pos_front.t' in tr.pos_front.t + (tr.pos_front.t).V/next 
	tr.pos_rear.t' in tr.pos_front.t' + (tr.pos_front.t').prev
	tr.pos_rear.t' in tr.pos_rear.t + (tr.pos_rear.t).V/next

	-- posibility to report PTD
	{
		t in tr.connected
		t' in tr.report_rear => t' in tr.report_front
	} || {
		t' not in tr.report_front
		t' not in tr.report_rear
	}

	-- if connected, follow MA
	t in tr.connected => tr.pos_front.t' in MAs[t',tr]

	-- frame condition
	t in tr.connected iff t' in tr.connected
}

-- start of mission action
pred som[t,t':Time,tr:Train] {
	tr not in connected.t
	connected.t' = connected.t + tr
	
	report_rear.t' = report_rear.t + tr
	report_front.t' = report_front.t + tr

	-- frame conditions
	pos_front.t' = pos_front.t
	pos_rear.t' = pos_rear.t
}

-- end of mission action
pred eom[t,t':Time,tr:Train] {
	tr in connected.t
	connected.t' = connected.t - tr

	report_rear.t' = report_rear.t - tr
	report_front.t' = report_front.t - tr

	-- frame conditions
	pos_front.t' = pos_front.t
	pos_rear.t' = pos_rear.t
}

-- encodes the notion of two carriages being the same integral train:
-- historically has the same state.
pred integral[t:Time,tr,tr':Train] {
	all t0 : t.*T/prev {
		tr'.MA.t0 = tr.MA.t0
		tr'.pos_front.t0 = tr.pos_front.t0
		tr'.pos_rear.t0 = tr.pos_rear.t0
		t0 in tr'.report_front iff t0 in tr.report_front
		t0 in tr'.report_rear iff t0 in tr.report_rear
	}
}

-- encodes the breaking up of an two-carriage train into two.
-- front one reports lost integrity, rear one stays disconnecetd.
pred split [t,t':Time,tr,tr':Train] {
	tr != tr'
	integral[t,tr,tr']
	t' not in tr'.(report_rear+report_front)
	tr.pos_rear.t' in tr.pos_front.t + tr.pos_rear.t
	tr'.pos_front.t' = tr'.pos_front.t
	tr'.pos_rear.t' = tr'.pos_rear.t
	pos_rear.t' - (tr+tr') -> VSS = pos_rear.t - (tr+tr') -> VSS
	pos_front.t' - tr' -> VSS = pos_front.t - tr' -> VSS
	report_rear.t' = report_rear.t - (tr' + tr)
	report_front.t' = report_front.t - tr'
	t in tr'.connected
	t' not in tr'.connected
}

/** 
Overall system evolution.
**/

-- forces state to be correctly updated; every train may move in each step.
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
Operational scenarios of the HL3 concept.
**/

-- Scenario 1 - Normal running of a single train with integrity confirmed by external device
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

		tr.(pos_front+pos_rear).t0 = v11
		tr.(pos_front+pos_rear).t1 = v12
		tr.(pos_front+pos_rear).t2 = v12
		tr.(pos_front+pos_rear).t3 = v21
		tr.(pos_front+pos_rear).t4 = v21
		tr.(pos_front+pos_rear).t5 = v22
		tr.(pos_front+pos_rear).t6 = v23
		tr.(pos_front+pos_rear).t7 = v31

		// final state
		v31.state.t7 = Occupied
		(VSS-v31).state.t7 = Free
	}
	}
}

-- Scenario 2 - Splitting of a composite train with integrity confirmed by external device
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

		tr1.(pos_front+pos_rear).t0 = v12
		tr1.(pos_front+pos_rear).t2 = v21
		tr1.(pos_front+pos_rear).t3 = v22
		tr1.(pos_front+pos_rear).t4 = v23
		tr1.(pos_front+pos_rear).t5 = v31+v23
		tr1.(pos_front+pos_rear).t6 = v31
		tr1.(pos_front+pos_rear).t7 = v31

		tr2.(pos_front+pos_rear).t0 = v12
		tr2.(pos_front+pos_rear).t7 = v12

		tr2.MA.(t1.nexts) = v12

		// final state
		(v11+v12).state.t7 = Unknown
		v31.state.t7 = Occupied
		(v21+v22+v23+v32+v33).state.t7 = Free
	}
	}
}

-- Scenario 3 - Shadow train
-- NOTE: breaks if #1A is modelled as in the HL3 concept
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

		tr1.(pos_front+pos_rear).t0 = v12
		tr1.(pos_front+pos_rear).t2 = v21
		tr1.(pos_front+pos_rear).t3 = v22
		tr1.(pos_front+pos_rear).t4 = v23
		tr1.(pos_front+pos_rear).t5 = v31
		tr1.(pos_front+pos_rear).t6 = (v31+v32)
		tr1.(pos_front+pos_rear).t7 = v32
		tr1.(pos_front+pos_rear).t8 = v32

		tr2.(pos_front+pos_rear).t0 = v12
		tr2.(pos_front+pos_rear).t2 = v12
		tr2.(pos_front+pos_rear).t3 = v12
		tr2.(pos_front+pos_rear).t4 = v21
		tr2.(pos_front+pos_rear).t5 = v22
		tr2.(pos_front+pos_rear).t6 = v23
		tr2.(pos_front+pos_rear).t7 = v31
		tr2.(pos_front+pos_rear).t8 = v31

		tr2.MA.(t1.nexts) = v12

		// final state
		v31.state.t8 = Unknown
		v32.state.t8 = Ambiguous
		(VSS-(v31+v32)).state.t8 = Free
	}
	}
}

-- Scenario 4 - Start of Mission / End of Mission
-- NOTE: breaks if #5A is modelled as in the HL3 concept
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

		tr.(pos_front+pos_rear).t0 = v11
		tr.(pos_front+pos_rear).t1 = v11
		tr.(pos_front+pos_rear).t2 = v12
		tr.(pos_front+pos_rear).t3 = v21
		tr.(pos_front+pos_rear).t4 = v21
		tr.(pos_front+pos_rear).t5 = v22
		tr.(pos_front+pos_rear).t6 = v22
		tr.(pos_front+pos_rear).t7 = v22

		no disconnect_ptimer.t6
		some disconnect_ptimer.t7
		no mute_timer.t6
		some mute_timer.t7 

		// final state
		(v21+v22+v23).state.t7 = Unknown
		(v11+v12+v31+v32+v33).state.t7 = Free
	}
	}
}

-- Scenario 5 - Integrity lost
-- NOTE: model does not implement delays on TTD detection
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

		tr1.(pos_front+pos_rear).t0 = v12
		tr1.(pos_front+pos_rear).t2 = v21
		tr1.(pos_front+pos_rear).t3 = v22
		tr1.(pos_front+pos_rear).t4 = v23
		tr1.(pos_front+pos_rear).t5 = v23+v31
		tr1.(pos_front+pos_rear).t6 = v31
		tr1.(pos_front+pos_rear).t7 = v31

		tr2.(pos_front+pos_rear).t0 = v12
		tr2.(pos_front+pos_rear).t7 = v12

		tr2.MA.(t1.nexts) = v12

		// final state
		(v11+v12).state.t7 = Unknown
		v31.state.t7 = Occupied
		(v21+v22+v23+v32+v33).state.t7 = Free
	}
	}
}

-- Scenario 6 - Connection lost and reconnect within session
-- NOTE: breaks if #1A is modelled as in the HL3 concept
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

		tr1.(pos_front+pos_rear).t0 = v12
		tr1.(pos_front+pos_rear).t1 = v12
		tr1.(pos_front+pos_rear).t2 = v12
		tr1.(pos_front+pos_rear).t3 = v21
		tr1.(pos_front+pos_rear).t4 = v22
		tr1.(pos_front+pos_rear).t5 = v22
		tr1.(pos_front+pos_rear).t6 = v23
		tr1.(pos_front+pos_rear).t7 = v31

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

-- Scenario 7 - Connection lost and reconnect within session with release of VSS
-- NOTE: breaks if #1A is modelled as in the HL3 concept
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

		tr1.(pos_front+pos_rear).t0 = v21
		tr1.(pos_front+pos_rear).t1 = v22
		tr1.(pos_front+pos_rear).t2 = v22
		tr1.(pos_front+pos_rear).t3 = v22
		tr1.(pos_front+pos_rear).t4 = v23
		tr1.(pos_front+pos_rear).t5 = v23+v31
		tr1.(pos_front+pos_rear).t6 = v23+v31
		tr1.(pos_front+pos_rear).t7 = v31
		tr1.(pos_front+pos_rear).t8 = v32

		tr1.mute_timer = t4+t5

		tr1.MA.Time = v32

		// final state
		v32.state.t8 = Occupied
		(VSS-v32).state.t8 = Free
	}
	}
}

-- Scenario 8 – Sweeping, jumping and two trains in a VSS
-- NOTE: trains can't enter or leave the track, modelled with "dummy" TTD
pred S8 {
	no ghost_ptimer + shadow_timer_A + shadow_timer_B + integrity_loss_ptimer + 
		disconnect_ptimer + mute_timer + integrity_timer

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

		tr1.(pos_front+pos_rear).(t0+t1) = v12
		tr1.(pos_front+pos_rear).t2 = v21
		tr1.(pos_front+pos_rear).t3 = v22
		tr1.(pos_front+pos_rear).t4 = v23
		tr1.(pos_front+pos_rear).(t5+t6) = v31
		tr1.(pos_front+pos_rear).t7 = v32
		tr1.(pos_front+pos_rear).t8 = v33
		tr1.(pos_front+pos_rear).(t9+t10) = v4
		
		tr2.(pos_front+pos_rear).t0 = v11
		tr2.(pos_front+pos_rear).t1 = v11+v12
		tr2.(pos_front+pos_rear).(t2+t3+t4) = v12
		tr2.(pos_front+pos_rear).(t5+t6) = v21
		tr2.(pos_front+pos_rear).(t7+t8) = v22
		tr2.(pos_front+pos_rear).t9 = v23
		tr2.(pos_front+pos_rear).t10 = v31
	
		// final state
		(v31).state.t10 = Occupied
		(VSS-(v31+v4)).state.t10 = Free
	}
	}
}

-- Scenario 9 – Ghost train
-- NOTE: breaks if indefinite timer expiration is implemented
-- NOTE: requires that the front report be processed before the rear report, must be forced
-- NOTE: trains can't enter or leave the track, modelled with "dummy" TTD
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

		tr1.(pos_front+pos_rear).(t0+t1+t2) = v23
		tr1.pos_front.t3 = v31
		tr1.pos_rear.t3 = v23
		tr1.pos_front.t4 = v32
		tr1.pos_rear.t4 = v31
		tr1.(pos_front+pos_rear).t6 = v32
		tr1.(pos_front+pos_rear).t7 = v32 + v33
		tr1.(pos_front+pos_rear).t9 = v33

		tr2.(pos_front+pos_rear).t0 = v0
		tr2.(pos_front+pos_rear).(t1+t2) = v11
		tr2.(pos_front+pos_rear).(t3+t4+t5+t6) = v12
		tr2.(pos_front+pos_rear).(t7+t8) = v21
		tr2.(pos_front+pos_rear).t9 = v22
	
		no ghost_ptimer.t1
		some ghost_ptimer.t2
		no ghost_ptimer.t7
	
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
Verification of safety properties.
**/

-- if all PTD information is consistent and no OS MAs, then only Free and Occupied states are assigned
assert trains_ok_states_ok {
	(init[T/first] && all t:Time | no mute[t] && no disintegrated[t] && all tr:Train | not OSMA[t.T/next,tr]) =>
		VSS.state.(T/first.nexts) in Free + Occupied
}

-- if all PTD information is consistent and no OS MAs, then Free is always correctly assigned (has no train)
assert trains_ok_free_ok {
	(init[T/first] && all t:Time | no mute[t] && no disintegrated[t] && all tr:Train | not OSMA[t.T/next,tr]) =>
		all t:Time | (VSS-Train.(pos_front+pos_rear).t).state.t = Free
}

-- if all PTD information is consistent and no OS MAs, then Occupied is always correctly assigned (has train)
assert trains_ok_occupied_ok {
	(init[T/first] && all t:Time | no mute[t] && no disintegrated[t] && all tr:Train | not OSMA[t.T/next,tr]) =>
		all t:Time | Train.(pos_front+pos_rear).t.state.t = Occupied
}

-- if all timers expire automatically, no OS MAs and trains don't move outside MAs,
-- then VSSs with a train are never Free
assert timers_auto_free_ok {
	(init[T/first] && all t:Time,tr:Train | auto_timer[t] && tr.pos_front.t in MAs[t,tr] && all tr:Train | not OSMA[t.T/next,tr]) =>
		all t:Time-last, tr:Train | (tr.pos_front.t).state.t != Free
}

-- if all timers expire automatically, no OS MAs and trains don't move outside MAs,
-- then Occupied VSSs have at most a train
assert timers_auto_occupied_ok {
	(init[T/first] && all t:Time,tr:Train | auto_timer[t] && tr.pos_front.t in MAs[t,tr] && all tr:Train | not OSMA[t.T/next,tr]) =>
		all t:Time-last, v:VSS| (v.state.t in Occupied) =>
			lone (pos_front.t + pos_rear.t).v
}

-- initial predicate, all trains reporting, all VSS states consistent, no expired timers.
pred init[t:Time] {
	some Train
	no mute_timer.t + integrity_timer.t + shadow_timer_A.t + shadow_timer_B.t + integrity_loss_ptimer.t + disconnect_ptimer.t
	Train = connected.t & report_rear.t & report_front.t
	all tr:Train | tr.pos_front.t = tr.pos_rear.t && tr.(pos_rear+pos_front).t.(state.t) = Occupied
	(VSS - (Train.(pos_rear+pos_front).t)).state.t = Free
	all tr:Train | tr.MA.t in tr.pos_front.t.*V/next &&
		all tr' : Train-tr | no MAs[t,tr] & MAs[t,tr']
}

-- forces all timers to expire as soon as start event is met
pred auto_timer [t:Time] {
	start_shadow_timer_A[t] in shadow_timer_A.t
	start_shadow_timer_B[t] in shadow_timer_B.t
	start_ghost_ptimer[t] in ghost_ptimer.t
	start_integrity_loss_ptimer[t] in integrity_loss_ptimer.t
	mute[t] in mute_timer.t
	all vs:VSS | some (knownTrain[t,vs])&mute_timer.t => vs in disconnect_ptimer.t
}

check trains_ok_states_ok		for 8 VSS, 3 TTD, 2 Train, 10 Time expect 0
check trains_ok_free_ok 		for 8 VSS, 3 TTD, 2 Train, 10 Time expect 0
check trains_ok_occupied_ok 	for 8 VSS, 3 TTD, 2 Train, 10 Time expect 0
check timers_auto_free_ok 		for 8 VSS, 3 TTD, 2 Train, 10 Time expect 0
check timers_auto_occupied_ok	for 8 VSS, 3 TTD, 2 Train, 10 Time expect 0

/**
Visualization auxiliary functions.
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

fun _Arear : Train -> Time { report_rear } 

