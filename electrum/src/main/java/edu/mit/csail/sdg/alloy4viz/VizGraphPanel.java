/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4viz;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.AdjustmentEvent;
import java.awt.event.AdjustmentListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.SwingConstants;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.OurBorder;
import edu.mit.csail.sdg.alloy4.OurCombobox;
import edu.mit.csail.sdg.alloy4.OurUtil;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.parser.Action2Alloy;
import edu.mit.csail.sdg.alloy4graph.GraphViewer;

/**
 * GUI panel that houses the actual graph, as well as any projection comboboxes.
 *
 * <p>
 * <b>Thread Safety:</b> Can be called only by the AWT event thread.
 */

public final class VizGraphPanel extends JPanel {

	/** This ensures the class can be serialized reliably. */
	private static final long serialVersionUID = 0;

	/** This is the current customization settings. */
	private final List<VizState> vizState;

	/** Whether the user wants to see the DOT source code or not. */
	private boolean seeDot = false;

	/** The current GraphViewer (or null if we are not looking at a GraphViewer) */
	private GraphViewer viewer = null;

	/** The scrollpane containing the upperhalf of the panel (showing the graph) */
	private final List<JScrollPane> diagramScrollPanels = new ArrayList<>();

	/** The upperhalf of the panel (showing the graph). */
	private final List<JPanel> graphPanels = new ArrayList<>();

	/**
	 * The lowerhalf of the panel (showing the comboboxes for choosing the projected
	 * atoms).
	 */
	private final JPanel navPanel;

	/** The splitpane separating the graphPanel and the navPanel. */
	private final JSplitPane split;

	/** The current projection choice; null if no projection is in effect. */
	private AlloyProjection currentProjection = null;

	/** This is the list of TypePanel(s) we've already constructed. */
	private final Map<AlloyType, TypePanel> type2panel = new TreeMap<AlloyType, TypePanel>();

	/**
	 * Inner class that displays a combo box of possible projection atom choices.
	 */
	final class TypePanel extends JPanel {
		/** This ensures the class can be serialized reliably. */
		private static final long serialVersionUID = 0;
		/** The type being projected. */
		private final AlloyType type;
		/**
		 * The list of atoms; can be an empty list if there are no atoms in this type to
		 * be projected.
		 */
		private final List<AlloyAtom> atoms;
		/** The list of atom names; atomnames.empty() iff atoms.isEmpty() */
		private final String[] atomnames;
		/** The combo box showing the possible atoms to choose from. */
		private final JComboBox atomCombo;

		/** True if this TypePanel object does not need to be rebuilt. */
		private boolean upToDate(AlloyType type, List<AlloyAtom> atoms) {
			if (!this.type.equals(type))
				return false;
			atoms = new ArrayList<AlloyAtom>(atoms);
			Collections.sort(atoms);
			if (!this.atoms.equals(atoms))
				return false;
			for (int i = 0; i < this.atoms.size(); i++) {
				String n = this.atoms.get(i).getVizName(vizState.get(0), true);
				if (!atomnames[i].equals(n))
					return false;
			}
			return true;
		}

		/**
		 * Constructs a new TypePanel.
		 * 
		 * @param type  - the type being projected
		 * @param atoms - the list of possible projection atom choices
		 */
		private TypePanel(AlloyType type, List<AlloyAtom> atoms, AlloyAtom initialValue) {
			super();
			final JButton left, right;
			int initialIndex = 0;
			this.type = type;
			atoms = new ArrayList<AlloyAtom>(atoms);
			Collections.sort(atoms);
			this.atoms = ConstList.make(atoms);
			setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
			setBorder(null);
			this.atomnames = new String[this.atoms.size()];
			for (int i = 0; i < this.atoms.size(); i++) {
				atomnames[i] = this.atoms.get(i).getVizName(vizState.get(0), true);
				if (this.atoms.get(i).equals(initialValue))
					initialIndex = i;
			}
			add(left = new JButton("<<"));
			add(Box.createRigidArea(new Dimension(2, 2)));
			add(atomCombo = new OurCombobox(atomnames.length < 1 ? new String[] { " " } : atomnames));
			add(Box.createRigidArea(new Dimension(2, 2)));
			add(right = new JButton(">>"));
			left.setVerticalAlignment(SwingConstants.CENTER);
			right.setVerticalAlignment(SwingConstants.CENTER);
			Dimension dim = atomCombo.getPreferredSize();
			int idealWidth = Util.onMac() ? 120 : 80;
			if (dim.width < idealWidth) {
				dim.width = idealWidth + 20;
				atomCombo.setMinimumSize(dim);
				atomCombo.setPreferredSize(dim);
			}
			left.setEnabled(initialIndex > 0);
			right.setEnabled(initialIndex < atomnames.length - 1);
			atomCombo.setSelectedIndex(initialIndex);
			if (Util.onMac())
				atomCombo.setBorder(BorderFactory.createEmptyBorder(4, 1, 0, 1));
			left.addActionListener(new ActionListener() {
				public final void actionPerformed(ActionEvent e) {
					int curIndex = atomCombo.getSelectedIndex();
					if (curIndex > 0)
						atomCombo.setSelectedIndex(curIndex - 1);
				}
			});
			right.addActionListener(new ActionListener() {
				public final void actionPerformed(ActionEvent e) {
					int curIndex = atomCombo.getSelectedIndex();
					if (curIndex < atomCombo.getItemCount() - 1)
						atomCombo.setSelectedIndex(curIndex + 1);
				}
			});
			atomCombo.addActionListener(new ActionListener() {
				public final void actionPerformed(ActionEvent e) {
					left.setEnabled(atomCombo.getSelectedIndex() > 0);
					right.setEnabled(atomCombo.getSelectedIndex() < atomnames.length - 1);
					remakeAll();
					VizGraphPanel.this.getParent().invalidate();
					VizGraphPanel.this.getParent().repaint();
				}
			});
		}

		/** Returns the entire list of atoms; could be an empty set. */
		public List<AlloyAtom> getAlloyAtoms() {
			return atoms;
		}

		/** Returns the currently-selected atom; returns null if the list is empty. */
		public AlloyAtom getAlloyAtom() {
			int i = atomCombo.getSelectedIndex();
			if (i >= 0 && i < atoms.size())
				return atoms.get(i);
			else
				return null;
		}

		/** Returns the AlloyType associated with this TypePanel. */
		public AlloyType getAlloyType() {
			return type;
		}
	}

	final VizGUI vizGUI;

	private JPopupMenu actionMenu;

	/**
	 * Create a splitpane showing the graph on top, as well as projection comboboxes
	 * on the bottom.
	 * 
	 * @param vizState - the current visualization settings
	 * @param seeDot   - true if we want to see the DOT source code, false if we
	 *                 want it rendered as a graph
	 * @param vizGUI
	 */
	public VizGraphPanel(List<VizState> vizState, boolean seeDot, VizGUI vizGUI) {
		this.vizGUI = vizGUI;
		Border b = new EmptyBorder(0, 0, 0, 0);
		OurUtil.make(this, Color.BLACK, Color.WHITE, b);
		this.seeDot = seeDot;
		this.vizState = vizState;
		setLayout(new GridLayout());
		setMaximumSize(new Dimension(Short.MAX_VALUE, Short.MAX_VALUE));
		navPanel = new JPanel();
		JScrollPane navscroll = OurUtil.scrollpane(navPanel);
		JPanel diagramsScrollPanel1 = new JPanel();
		diagramsScrollPanel1.setLayout(new BoxLayout(diagramsScrollPanel1, BoxLayout.LINE_AXIS));
		for (int i = 0; i < vizState.size(); i++) {

			JScrollPane split_ = createGraphPanel(i);
			diagramsScrollPanel1.add(split_);
			split_.setPreferredSize(new Dimension(0,0));
			
		}

		JPanel diagramsScrollPanel2 = new JPanel();
		diagramsScrollPanel2.add(Box.createHorizontalGlue());
		diagramsScrollPanel2.setLayout(new BoxLayout(diagramsScrollPanel2, BoxLayout.LINE_AXIS));
		for (int i = 0; i < vizState.size(); i++) {

			JPanel split2_ = createTempPanel(i);
			diagramsScrollPanel2.add(split2_);

			AlloyModel model = vizState.get(0).getOriginalModel();
			AlloyType event = model.hasType(Action2Alloy.ACTION_SIG); 
			if (event != null) {
				if (i < vizState.size() - 1) {
					diagramsScrollPanel2.add(Box.createHorizontalGlue());
					JPanel p = new JPanel();
					p.setLayout(new BoxLayout(p, BoxLayout.LINE_AXIS));
					JPanel aux = new JPanel();
					JButton branch = new JButton(new String(Character.toChars(0x21dd)));
					branch.setPreferredSize(new Dimension(60, 30));
					branch.setMinimumSize(new Dimension(60, 30));

					actionMenu = new JPopupMenu("Menu");
					branch.addMouseListener(new MouseAdapter() {
						public void mouseReleased(MouseEvent e) {
							if (e.getButton() == 1) {
								actionMenu.show(e.getComponent(), e.getX(), e.getY());
							}
						}
					});
					
					JLabel action = new JLabel("ActionAction[arg1,arg2]", SwingConstants.CENTER);
					action.setFont(action.getFont().deriveFont(Font.BOLD));
					action.setMinimumSize(action.getPreferredSize());
					action.setMaximumSize(action.getPreferredSize());
					action.setPreferredSize(action.getPreferredSize());
					this.actionLabel.add(action);
					
					aux.add(action);
					aux.add(branch);
					aux.setLayout(new BoxLayout(aux, BoxLayout.LINE_AXIS));
					p.add(aux);

					diagramsScrollPanel2.add(p);
					diagramsScrollPanel2.add(Box.createHorizontalGlue());
				}
			}

		}
		diagramsScrollPanel2.add(Box.createHorizontalGlue());

		diagramsScrollPanel1.setPreferredSize(new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE));
		JSplitPane diagramsScrollPanel = OurUtil.splitpane(JSplitPane.VERTICAL_SPLIT, diagramsScrollPanel1, diagramsScrollPanel2, 0);
		diagramsScrollPanel.setLayout(new BoxLayout(diagramsScrollPanel, BoxLayout.PAGE_AXIS));
		diagramsScrollPanel.setResizeWeight(1.0);
		diagramsScrollPanel.setDividerSize(0);
		split = OurUtil.splitpane(JSplitPane.VERTICAL_SPLIT, diagramsScrollPanel, navscroll, 0);
		split.setResizeWeight(1.0);
		split.setDividerSize(0);
		add(split);
		
		addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				int key = e.getKeyCode();
				if (key == KeyEvent.VK_LEFT) {
					if (current > 0)
						current--;
					updateTmps();
				}
				if (key == KeyEvent.VK_RIGHT) {
					current++;
					updateTmps();
				}
			}
		});
		
		updateTmps();
		remakeAll();
	}

	private JScrollPane createGraphPanel(int i) {
		Border b = new EmptyBorder(0, 0, 0, 0);

		JPanel graphPanel = OurUtil.make(new JPanel(), Color.BLACK, Color.WHITE, b);
		graphPanels.add(graphPanel);
		graphPanel.addMouseListener(new MouseAdapter() {
			@Override
			public void mousePressed(MouseEvent ev) {
				// We let Ctrl+LeftClick bring up the popup menu, just like RightClick,
				// since many Mac mouses do not have a right button.
				if (viewer == null)
					return;
				else if (ev.getButton() == MouseEvent.BUTTON3) {
				} else if (ev.getButton() == MouseEvent.BUTTON1 && ev.isControlDown()) {
				} else
					return;
				viewer.alloyPopup(graphPanel, ev.getX(), ev.getY());
			}
		});

		JScrollPane diagramScrollPanel = OurUtil.scrollpane(graphPanel, new OurBorder(true, true, true, false));
		diagramScrollPanel.getVerticalScrollBar().addAdjustmentListener(new AdjustmentListener() {
			public void adjustmentValueChanged(AdjustmentEvent e) {
				diagramScrollPanel.invalidate();
				diagramScrollPanel.repaint();
				diagramScrollPanel.validate();
			}
		});
		diagramScrollPanel.getHorizontalScrollBar().addAdjustmentListener(new AdjustmentListener() {
			public void adjustmentValueChanged(AdjustmentEvent e) {
				diagramScrollPanel.invalidate();
				diagramScrollPanel.repaint();
				diagramScrollPanel.validate();
			}
		});
		diagramScrollPanels.add(diagramScrollPanel);
		return diagramScrollPanel;
	}
	
	// TODO: push this back up to vizgui, avoids passing vizgui here
	private JPanel createTempPanel(int i) {
		JPanel tmpPanel = new JPanel();
		tmpPanel.setLayout(new BoxLayout(tmpPanel, BoxLayout.LINE_AXIS));

		JButton leftTime = new JButton(new String(Character.toChars(0x2190)));
		this.leftTime.add(leftTime);
		JButton rightTime = new JButton(new String(Character.toChars(0x2192)));
		this.rightTime.add(rightTime);
		leftTime.setEnabled(false);
		rightTime.setEnabled(false);
		rightTime.setMaximumSize(new Dimension(1,1));
		leftTime.setMaximumSize(new Dimension(1,1));
		rightTime.setMinimumSize(new Dimension(1,1));
		leftTime.setMinimumSize(new Dimension(1,1));
		JLabel timeLabel = new JLabel("State 99 (99) 999", SwingConstants.CENTER);
		timeLabel.setFont(timeLabel.getFont().deriveFont(Font.BOLD));
		timeLabel.setMinimumSize(timeLabel.getPreferredSize());
		timeLabel.setMaximumSize(timeLabel.getPreferredSize());
		timeLabel.setPreferredSize(timeLabel.getPreferredSize());
		this.timeLabel.add(timeLabel);
		JLabel tempMsg = new JLabel("");
		this.tempMsg.add(tempMsg);

		JButton nextButton = new JButton(new String(Character.toChars(0x21ba)));
		nextButton.setPreferredSize(new Dimension(40, rightTime.getHeight()));

		nextButton.addActionListener(new ActionListener() {
			public final void actionPerformed(ActionEvent e) {
				vizGUI.doNext(current+i);
				updateTmps();
			}
		});
		leftTime.addActionListener(new ActionListener() {
			public final void actionPerformed(ActionEvent e) {
				if (current > 0)
					current--;
				updateTmps();
			}
		});
		rightTime.addActionListener(new ActionListener() {
			public final void actionPerformed(ActionEvent e) {
				current++;
				updateTmps();
			}
		});
		

		JPanel aux = new JPanel();
		aux.setLayout(new GridLayout());
		aux.add(leftTime);
		aux.setPreferredSize(new Dimension(60, 30));
		aux.setMaximumSize(new Dimension(60,30));
		tmpPanel.add(aux);
		tmpPanel.add(timeLabel);
		tmpPanel.add(nextButton);
		aux = new JPanel();
		aux.setLayout(new GridLayout());
		aux.add(rightTime);
		aux.setPreferredSize(new Dimension(60, 30));
		aux.setMaximumSize(new Dimension(60,30));
		tmpPanel.add(aux);

		if (i != vizState.size() - 1)
			rightTime.setVisible(false);
		if (i != 0)
			leftTime.setVisible(false);

		return tmpPanel;
	}
	
	void enableAct(String k, boolean enab) {
		for (Component m : actionMenu.getComponents())
			if (((JMenuItem) m).getText().equals(k.substring(1))) {
				m.setEnabled(enab);
				if (enab) m.setForeground(new Color(0,128,0));
			}
	}

	private void updateTmps() {
		int backindex = vizState.get(0).getOriginalInstance().originalA4.getLoopState();
		int length = 1 + vizState.get(0).getOriginalInstance().originalA4.getLastState();
		if (actionMenu!=null) actionMenu.removeAll();

		for (int i = 0; i < timeLabel.size(); i++) {
			int c = current + i;
			int llen = length - backindex;
			if (c>backindex) c = ((c-backindex)%llen)+backindex;
			timeLabel.get(i).setText("State " + (current + i) + (c==(current+i)? "" : " (" + new String(Character.toChars(0x2261)) + c + ")"));
			if (current+i > 0) {
				leftTime.get(i).setEnabled(true);
				leftTime.get(i).setText(new String(Character.toChars(0x2190)));
			} else {
				leftTime.get(i).setEnabled(false);
				leftTime.get(i).setText(new String(Character.toChars(0x21e4)));
			}
			rightTime.get(i).setEnabled(true);

			if (c == length - 1) {
				rightTime.get(i).setText(new String(Character.toChars(0x21b6)) + backindex);
				timeLabel.get(i).setFont(timeLabel.get(i).getFont().deriveFont(Font.BOLD));
				if (c == backindex) {
					timeLabel.get(i).setForeground(new Color(13, 152, 186));
					tempMsg.get(i).setText("Loop starts and ends here.");
					timeLabel.get(i).setText(timeLabel.get(i).getText()+new String(Character.toChars(0x21c5)));
				}
				else {
					timeLabel.get(i).setForeground(new Color(65,105,225));
					tempMsg.get(i).setText("Last state before looping.");
					timeLabel.get(i).setText(timeLabel.get(i).getText()+new String(Character.toChars(0x2191)));
				}
			} else {
				rightTime.get(i).setText(new String(Character.toChars(0x2192)));
				// change text when loop state
				if (c == backindex) {
					timeLabel.get(i).setFont(timeLabel.get(i).getFont().deriveFont(Font.BOLD));
					timeLabel.get(i).setForeground(new Color(0,128,0));
					timeLabel.get(i).setText(timeLabel.get(i).getText()+new String(Character.toChars(0x2193)));
					tempMsg.get(i).setText("Loop starts here.");
				} else {
					timeLabel.get(i).setFont(timeLabel.get(i).getFont().deriveFont(Font.PLAIN));
					timeLabel.get(i).setForeground(Color.BLACK);
					tempMsg.get(i).setText("");
				}
			}
			
			AlloyInstance myInstance;
			File f = new File(vizGUI.getXMLfilename());
			try {
				if (!f.exists())
					throw new IOException("File " + vizGUI.getXMLfilename() + " does not exist.");
				myInstance = StaticInstanceReader.parseInstance(f, current + i); 
				vizState.get(i).loadInstance(myInstance);
			} catch (Throwable e) {
				System.out.println("a");
			}
			
			AlloyModel model = vizState.get(0).getOriginalModel();
			AlloyType event = model.hasType(Action2Alloy.ACTION_SIG); 
			if (event != null) {
				List<AlloyType> events = model.getSubTypes(event);
				if (i < vizState.size() - 1) {
					for (AlloyType ev : events) {
						final int j = i;
						JMenuItem item = new JMenuItem(ev.getName().substring(1));
						item.addActionListener(new ActionListener() {
							@Override
							public void actionPerformed(ActionEvent e) {
								vizGUI.doNext(j,ev.getName());
							}
						});
						actionMenu.add(item);
					}
					
					final int jj = current + i;
					Thread thread = new Thread() {
						public void run() {
							String[] as = (String[]) events.stream().map(e -> e.getName()).toArray(String[]::new);
							vizGUI.hasNexts(jj,as);
						}
					};
					thread.start();
					
					AlloyInstance inst = vizState.get(i).getOriginalInstance();
					// find the type of the event fired in this instance, may be more than one due to args
					AlloyTuple firedargs = null;
					for(AlloyRelation r:model.getRelations()) 
						if (r.getName().equals(Action2Alloy.FIRED_REL) && !inst.relation2tuples(r).isEmpty()) 
							firedargs = inst.relation2tuples(r).iterator().next();
					
					StringBuilder sb = new StringBuilder();
					AlloyType firedtype = firedargs.getAtoms().get(1).getType();					
					sb.append(firedtype.getName().substring(1));
					sb.append('[');
					// find the actual arguments of the fired event
					for (int j = 2; j < firedargs.getArity(); j++) {
						if (!firedargs.getAtoms().get(j).toString().equals("_Dummy0")) {
						sb.append(firedargs.getAtoms().get(j).toString());
							if (j < firedargs.getArity()-1)
								sb.append(',');
						}
					}
					sb.append(']');
					actionLabel.get(i).setText(sb.toString());
				}
			}
			

		}
		remakeAll();
	}

	// ========================================TRACES=====================================================//

	private int current = 0;
	
	public int currentState() {
		return current;
	}
	
	public void rollback(int state) {
		current = state;
		updateTmps();
	}
	
	/** Trace navigation combo box. */
	// [HASLab]
	private List<JLabel> timeLabel = new ArrayList<JLabel>();

	/** Trace navigation buttons. */
	private List<JButton> leftTime = new ArrayList<JButton>(), rightTime = new ArrayList<JButton>();

	private List<JLabel> actionLabel = new ArrayList<JLabel>();

	/** Optional message to be displayed. */
	// [HASLab]
	private List<JLabel> tempMsg = new ArrayList<JLabel>();

	/** Regenerate the comboboxes and the graph. */
	public void remakeAll() {
		Map<AlloyType, AlloyAtom> map = new LinkedHashMap<AlloyType, AlloyAtom>();
		navPanel.removeAll();
		for (int i = 0; i < vizState.size(); i++) {
			for (AlloyType type : vizState.get(i).getProjectedTypes()) {
				List<AlloyAtom> atoms = vizState.get(i).getOriginalInstance().type2atoms(type);
				TypePanel tp = type2panel.get(type);
				if (tp != null && tp.getAlloyAtom() != null && !atoms.contains(tp.getAlloyAtom()))
					tp = null;
				if (tp != null && tp.getAlloyAtom() == null && atoms.size() > 0)
					tp = null;
				if (tp != null && !tp.upToDate(type, atoms))
					tp = null;
				if (tp == null)
					type2panel.put(type, tp = new TypePanel(type, atoms, null));
				navPanel.add(tp);
				map.put(tp.getAlloyType(), tp.getAlloyAtom());
			}
			currentProjection = new AlloyProjection(map);
			JPanel graph = vizState.get(i).getGraph(currentProjection);
			if (seeDot && (graph instanceof GraphViewer)) {
				viewer = null;
				JTextArea txt = OurUtil.textarea(graph.toString(), 10, 10, false, true, getFont());
				diagramScrollPanels.get(i).setViewportView(txt);
			} else {
				if (graph instanceof GraphViewer)
					viewer = (GraphViewer) graph;
				else
					viewer = null;
				graphPanels.get(i).removeAll();
				graphPanels.get(i).add(graph);
				diagramScrollPanels.get(i).setViewportView(graphPanels.get(i));
				diagramScrollPanels.get(i).invalidate();
				diagramScrollPanels.get(i).repaint();
				diagramScrollPanels.get(i).validate();
			}
			vizState.get(i).applyDefaultVar(); // [HASLab] dashed variable elements
		}
	}

	/** Changes the font. */
	@Override
	public void setFont(Font font) {
		super.setFont(font);
		if (diagramScrollPanels != null)
			for (JScrollPane diagramScrollPanel : diagramScrollPanels)
				diagramScrollPanel.getViewport().getView().setFont(font);
	}

	/** Changes whether we are seeing the DOT source or not. */
	public void seeDot(boolean yesOrNo) {
		if (seeDot == yesOrNo)
			return;
		seeDot = yesOrNo;
		remakeAll();
	}

	public String toDot() {
		return vizState.get(0).getGraph(currentProjection).toString();
	}

	/**
	 * Retrieves the actual GraphViewer object that contains the graph (or null if
	 * the graph hasn't loaded yet)
	 */
	public GraphViewer alloyGetViewer() {
		return viewer;
	}

	/** We override the paint method to auto-resize the divider. */
	@Override
	public void paint(Graphics g) {
		super.paint(g);
		split.setDividerLocation(split.getSize().height - split.getInsets().bottom - split.getDividerSize()
				- split.getRightComponent().getPreferredSize().height);
	}

	public void resetProjectionAtomCombos() {
		for (Entry<AlloyType, TypePanel> e : type2panel.entrySet()) {
			if (e.getValue().atomCombo != null)
				e.getValue().atomCombo.setSelectedIndex(0);
		}
	}

}