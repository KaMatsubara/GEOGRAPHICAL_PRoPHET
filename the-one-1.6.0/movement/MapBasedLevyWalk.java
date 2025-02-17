/* 
 * Copyright 2010 Aalto University, ComNet
 * Released under GPLv3. See LICENSE.txt for details. 
 */
package movement;

import java.io.File;
import java.io.IOException;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Vector;

import core.Coord;
import core.Settings;
import core.SettingsError;
import core.SimError;
import input.WKTMapReader;
import movement.map.MapNode;
import movement.map.SimMap;

/**
 * Map based movement model which gives out Paths that use the
 * roads of a SimMap. 
 */
public class MapBasedLevyWalk extends MovementModel implements SwitchableMovement {
	/** sim map for the model */
	private SimMap map = null;
	/** node where the last path ended or node next to initial placement */
	protected MapNode lastMapNode;
	/**  max nrof map nodes to travel/path */
	protected int maxPathLength = 100;
	/**  min nrof map nodes to travel/path */
	protected int minPathLength = 10;
	/**  べき指数 */
	protected double lambda = 1.2;
	/** May a node choose to move back the same way it came at a crossing */
	protected boolean backAllowed;
	/** map based movement model's settings namespace ({@value})*/
	public static final String MAP_BASE_MOVEMENT_NS = "MapBasedLevyWalk";
	/** number of map files -setting id ({@value})*/
	public static final String NROF_FILES_S = "nrofMapFiles";
	/** map file -setting id ({@value})*/
	public static final String FILE_S = "mapFile";
	public Double permissibleError = 180.0;
	
	/** 
	 * Per node group setting for selecting map node types that are OK for
	 * this node group to traverse trough. Value must be a comma separated list
	 * of integers in range of [1,31]. Values reference to map file indexes
	 * (see {@link #FILE_S}). If setting is not defined, all map nodes are 
	 * considered OK.
	 */
	public static final String MAP_SELECT_S = "okMaps";
	
	/** the indexes of the OK map files or null if all maps are OK */
	private int [] okMapNodeTypes;
	
	/** how many map files are read */
	private int nrofMapFilesRead = 0;
	/** map cache -- in case last mm read the same map, use it without loading*/
	private static SimMap cachedMap = null;
	/** names of the previously cached map's files (for hit comparison) */
	private static List<String> cachedMapFiles = null;

	SecureRandom random = new SecureRandom();
	
	/**
	 * Creates a new MapBasedMovement based on a Settings object's settings.
	 * @param settings The Settings object where the settings are read from
	 */
	public MapBasedLevyWalk(Settings settings) {
		super(settings);
		map = readMap();
		readOkMapNodeTypes(settings);
		maxPathLength = 100;
		minPathLength = 10;
		backAllowed = false;
	}

	/**
	 * Creates a new MapBasedMovement based on a Settings object's settings
	 * but with different SimMap
	 * @param settings The Settings object where the settings are read from
	 * @param newMap The SimMap to use
	 * @param nrofMaps How many map "files" are in the map
	 */	
	public MapBasedLevyWalk(Settings settings, SimMap newMap, int nrofMaps) {
		super(settings);
		map = newMap;
		this.nrofMapFilesRead = nrofMaps;
		readOkMapNodeTypes(settings);
		maxPathLength = 100;
		minPathLength = 10;
		backAllowed = false;
	}
	
	/**
	 * Reads the OK map node types from settings
	 * @param settings The settings where the types are read
	 */
	private void readOkMapNodeTypes(Settings settings) {
		if (settings.contains(MAP_SELECT_S)) {
			this.okMapNodeTypes = settings.getCsvInts(MAP_SELECT_S);
			for (int i : okMapNodeTypes) {
				if (i < MapNode.MIN_TYPE || i > MapNode.MAX_TYPE) {
					throw new SettingsError("Map type selection '" + i + 
							"' is out of range for setting " + 
							settings.getFullPropertyName(MAP_SELECT_S));
				}
				if (i > nrofMapFilesRead) {
					throw new SettingsError("Can't use map type selection '" + i
							+ "' for setting " + 
							settings.getFullPropertyName(MAP_SELECT_S)
							+ " because only " + nrofMapFilesRead + 
							" map files are read");
				}
			}
		}
		else {
			this.okMapNodeTypes = null;
		}		
	}
	
	/**
	 * Copyconstructor.
	 * @param mbm The MapBasedMovement object to base the new object to 
	 */
	protected MapBasedLevyWalk(MapBasedLevyWalk mbl) {
		super(mbl);
		this.okMapNodeTypes = mbl.okMapNodeTypes;
		this.map = mbl.map;
		this.minPathLength = mbl.minPathLength;
		this.maxPathLength = mbl.maxPathLength;
		this.backAllowed = mbl.backAllowed;
	}
	
	/**
	 * Returns a (random) coordinate that is between two adjacent MapNodes
	 */
	@Override
	public Coord getInitialLocation() {
		List<MapNode> nodes = map.getNodes();
		MapNode n,n2;
		Coord n2Location, nLocation, placement;
		double dx, dy;
		double rnd = rng.nextDouble();
		
		// choose a random node (from OK types if such are defined)
		do {
			n = nodes.get(rng.nextInt(nodes.size()));
		} while (okMapNodeTypes != null && !n.isType(okMapNodeTypes));
		
		// choose a random neighbor of the selected node
		n2 = n.getNeighbors().get(rng.nextInt(n.getNeighbors().size())); 
		
		nLocation = n.getLocation();
		n2Location = n2.getLocation();
		
		placement = n.getLocation().clone();
		
		dx = rnd * (n2Location.getX() - nLocation.getX());
		dy = rnd * (n2Location.getY() - nLocation.getY());
		
		placement.translate(dx, dy); // move coord from n towards n2
		
		this.lastMapNode = n;
		return placement;
	}
	
	/**
	 * Returns map node types that are OK for this movement model in an array
	 * or null if all values are considered ok
	 * @return map node types that are OK for this movement model in an array
	 */
	protected int[] getOkMapNodeTypes() {
		return okMapNodeTypes;
	}
	
	@Override
	public Path getPath() {
		Path p = new Path(generateSpeed());
		MapNode curNode = lastMapNode;
		MapNode prevNode = lastMapNode;
		MapNode nextNode = null;	
		List<MapNode> neighbors;
		Coord nextCoord;
		Double orientation = this.getOrientation(); // 方向を決定
		
		assert lastMapNode != null: "Tried to get a path before placement";
		
		// start paths from current node 
		p.addWaypoint(curNode.getLocation());
		
		int pathLength = (int)Math.round((minPathLength * levyGenerateor()));

		for (int i=0; i<pathLength; i++) {
			neighbors = curNode.getNeighbors();
			Vector<MapNode> n2 = new Vector<MapNode>(neighbors);
			Vector<MapNode> possibleNeighbors = new Vector<MapNode>();
			if (!this.backAllowed) {
				n2.remove(prevNode); // to prevent going back
			}
				
			if (okMapNodeTypes != null) { //remove neighbor nodes that aren't ok
				for (int j=0; j < n2.size(); ){
					if (!n2.get(j).isType(okMapNodeTypes)) {
						n2.remove(j);
					}
					else {
						j++;
					}
				}
			}
			
			if (n2.size() == 0) { // only option is to go back
				nextNode = prevNode;
			}
			else { // 適当なノードを選ぶ
				 while (possibleNeighbors.size() < 1) // 移動可能なエッジを見つけるまで繰り返す
                 {
					 for(MapNode n : n2) {
							Double error = this.getError(orientation, curNode,n); // 方向と隣接エッジとの誤差を取得
		                    if (error < this.permissibleError) {
		                        possibleNeighbors.add(n); // 許容誤差内であれば、移動可能とする
		                    }
						}

                     if (possibleNeighbors.size() < 1) { // 移動可能なエッジが存在しない場合                        
                             // 新たに方向を取得する（そして、また移動可能なエッジを調べる）
                             orientation = this.getOrientation();
                     }
                 }
				
				
				 // 移動可能なエッジの中からもっとも誤差が小さいエッジを取得
				 MapNode bestNode = this.getMinimumError(orientation,possibleNeighbors,curNode);
				 nextNode = bestNode;
			}
			
			prevNode = curNode;
		
			nextCoord = nextNode.getLocation();
			curNode = nextNode;
			
			p.addWaypoint(nextCoord);
		}
		
		lastMapNode = curNode;

		return p;
	}
	
	/**
	 * Selects and returns a random node that is OK from a list of nodes.
	 * Whether node is OK, is determined by the okMapNodeTypes list.
	 * If okMapNodeTypes are defined, the given list <strong>must</strong>
	 * contain at least one OK node to prevent infinite looping.
	 * @param nodes The list of nodes to choose from.
	 * @return A random node from the list (that is OK if ok list is defined)
	 */
	protected MapNode selectRandomOkNode(List<MapNode> nodes) {
		MapNode n;
		do {
			n = nodes.get(rng.nextInt(nodes.size()));
		} while (okMapNodeTypes != null && !n.isType(okMapNodeTypes));

		return n;
	}
	
	/**
	 * Returns the SimMap this movement model uses
	 * @return The SimMap this movement model uses
	 */
	public SimMap getMap() {
		return map;
	}
	
	/**
	 * Reads a sim map from location set to the settings, mirrors the map and
	 * moves its upper left corner to origo.
	 * @return A new SimMap based on the settings
	 */
	private SimMap readMap() {
		SimMap simMap;
		Settings settings = new Settings(MAP_BASE_MOVEMENT_NS);
		WKTMapReader r = new WKTMapReader(true);
		
		if (cachedMap == null) {
			cachedMapFiles = new ArrayList<String>(); // no cache present
		}
		else { // something in cache
			// check out if previously asked map was asked again
			SimMap cached = checkCache(settings);
			if (cached != null) {
				nrofMapFilesRead = cachedMapFiles.size();
				return cached; // we had right map cached -> return it
			}
			else { // no hit -> reset cache
				cachedMapFiles = new ArrayList<String>();
				cachedMap = null;
			}
		}

		try {
			int nrofMapFiles = settings.getInt(NROF_FILES_S);

			for (int i = 1; i <= nrofMapFiles; i++ ) {
				String pathFile = settings.getSetting(FILE_S + i);
				cachedMapFiles.add(pathFile);
				r.addPaths(new File(pathFile), i);
			}
			r.getCDN().calcCDMap();
			
			nrofMapFilesRead = nrofMapFiles;
		} catch (IOException e) {
			throw new SimError(e.toString(),e);
		}

		simMap = r.getMap();
		checkMapConnectedness(simMap.getNodes());
		// mirrors the map (y' = -y) and moves its upper left corner to origo
		simMap.mirror();
		Coord offset = simMap.getMinBound().clone();		
		simMap.translate(-offset.getX(), -offset.getY());
		checkCoordValidity(simMap.getNodes());
		
		cachedMap = simMap;
		return simMap;
	}
	
	/**
	 * Checks that all map nodes can be reached from all other map nodes
	 * @param nodes The list of nodes to check
	 * @throws SettingsError if all map nodes are not connected
	 */
	private void checkMapConnectedness(List<MapNode> nodes) {
		Set<MapNode> visited = new HashSet<MapNode>();
		Queue<MapNode> unvisited = new LinkedList<MapNode>();
		MapNode firstNode;
		MapNode next = null;
		
		if (nodes.size() == 0) {
			throw new SimError("No map nodes in the given map");
		}
		
		firstNode = nodes.get(0);
		
		visited.add(firstNode);
		unvisited.addAll(firstNode.getNeighbors());
		
		while ((next = unvisited.poll()) != null) {
			visited.add(next);
			for (MapNode n: next.getNeighbors()) {
				if (!visited.contains(n) && ! unvisited.contains(n)) {
					unvisited.add(n);
				}
			}
		}
		
		if (visited.size() != nodes.size()) { // some node couldn't be reached
			MapNode disconnected = null;
			for (MapNode n : nodes) { // find an example node
				if (!visited.contains(n)) {
					disconnected = n;
					break;
				}
			}
			throw new SettingsError("SimMap is not fully connected. Only " + 
					visited.size() + " out of " + nodes.size() + " map nodes " +
					"can be reached from " + firstNode + ". E.g. " + 
					disconnected + " can't be reached");
		}
	}
	
	/**
	 * Checks that all coordinates of map nodes are within the min&max limits
	 * of the movement model
	 * @param nodes The list of nodes to check
	 * @throws SettingsError if some map node is out of bounds
	 */
	private void checkCoordValidity(List<MapNode> nodes) {
		 // Check that all map nodes are within world limits
		for (MapNode n : nodes) {
			double x = n.getLocation().getX();
			double y = n.getLocation().getY();
			if (x < 0 || x > getMaxX() || y < 0 || y > getMaxY()) {
				throw new SettingsError("Map node " + n.getLocation() + 
						" is out of world  bounds "+
						"(x: 0..." + getMaxX() + " y: 0..." + getMaxY() + ")");
			}
		}
	}
	
	/**
	 * Checks map cache if the requested map file(s) match to the cached
	 * sim map
	 * @param settings The Settings where map file names are found 
	 * @return A cached map or null if the cached map didn't match
	 */
	private SimMap checkCache(Settings settings) {
		int nrofMapFiles = settings.getInt(NROF_FILES_S);

		if (nrofMapFiles != cachedMapFiles.size() || cachedMap == null) {
			return null; // wrong number of files
		}
		
		for (int i = 1; i <= nrofMapFiles; i++ ) {
			String pathFile = settings.getSetting(FILE_S + i);
			if (!pathFile.equals(cachedMapFiles.get(i-1))) {
				return null;	// found wrong file name
			}
		}
		
		// all files matched -> return cached map
		return cachedMap;
	}
	
	@Override
	public MapBasedLevyWalk replicate() {
		return new MapBasedLevyWalk(this);
	}
	
	public Coord getLastLocation() {
		if (lastMapNode != null) {
			return lastMapNode.getLocation();
		} else {
			return null;
		}
	}

	public void setLocation(Coord lastWaypoint) {
		// TODO: This should be optimized
		MapNode nearest = null;
		double minDistance = Double.MAX_VALUE;
		Iterator<MapNode> iterator = getMap().getNodes().iterator();
		while (iterator.hasNext()) {
			MapNode temp = iterator.next();
			double distance = temp.getLocation().distance(lastWaypoint);
			if (distance < minDistance) {
				minDistance = distance;
				nearest = temp;
			}
		}
		lastMapNode = nearest;
	}

	public boolean isReady() {
		return true;
	}

	public Double getRandomValue() {
        Double aValue = random.nextDouble(); // 乱数を取得
        return aValue; // 0 <= d < 1
    }
	
	public Double levyGenerateor(){
		Double value = Math.pow(this.getRandomValue(), (-1) / this.lambda); // x^(-λ) べき関数
		if (value < 1) {
			System.err.println("aHopValue < 1, " + value);
			System.exit(1);
		} else if (value > 10000.0) {
			value = 10000.0;
		}
		return value;
	}
	
	public Double getOrientation() {
        Integer valueInt = Integer.valueOf(this.random.nextInt(360)); // 0<=x<360ので角度(移動方向)を取得
        Double orientation = Double.valueOf(valueInt.doubleValue()); // 取得した角度を少数に変換
        return orientation;
    }
	
	public Double getAngle(MapNode own, MapNode other) {
        
        Double x = other.getLocation().getX() - own.getLocation().getX(); // x座標を取得
        Double y = other.getLocation().getY() - own.getLocation().getY(); // y座標を取得
        Double anAngle = Math.toDegrees(Math.atan2(x, y)); // ラジアンではなく、度を取得
        

        return anAngle;
    }
	
	public Double getError(Double anOrientation, MapNode own, MapNode other) {
        Double anAngle = this.getAngle(own,other);
        Double anError = anAngle - anOrientation;
        return Math.abs(anError); // 絶対値で返す
    }
	
	public MapNode getMinimumError(Double anOrientation,Vector<MapNode>   anArray, MapNode own) {
        Double minimumError = this.permissibleError + Double.valueOf(1.0);
        MapNode minimumNode = anArray.get(0); // 初期化

        for (MapNode anNode : anArray) {
            Double error = getError(anOrientation,own,anNode);
            if (minimumError > error) {
                minimumError = error; // 比較演算は使わないほうが良い？？？
                minimumNode = anNode;
            }
        }

        return minimumNode;
    }
	
	
}

