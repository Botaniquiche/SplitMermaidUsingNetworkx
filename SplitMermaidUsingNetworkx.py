# Core functionality
import json
import networkx as nx          # Graph library for creating and manipulating network structures
import re                      # Regular expressions for pattern matching and text processing
# Core system functionalities
import sys                     # Access to command-line arguments and system-specific parameters
import subprocess              # Spawning and controlling external processes
import os                      # Operating system interface for file and directory operations
from pathlib import Path       # Object-oriented filesystem path manipulation
import glob                    # File path pattern matching with wildcard support

# Visualization and PDF processing
import matplotlib.pyplot as plt # Plotting library for creating visualizations (debug only)
from pprint import pprint      # Pretty printing of complex data structures (debug only)
import fitz                    # PyMuPDF library for PDF manipulation and scaling

# Data formats and typing
from ruamel.yaml import YAML, YAML  # Advanced YAML parser with better error handling and comment preservation
from typing import Dict, Any    # Type hints for better code documentation and IDE support

# Utility functions
import gc                      # Garbage collector control for memory management


###### CHANGELOG AND USAGE WARNING ######
## Usage possible only if:
##   - No multiple link on same line (i.e. no "A & B --> C & D" or similar)
##   - No Node_Text on several lines! If needed in the node text, build string with "<br/>" tags to break lines
## v0.1
## - First version
# TODO CHECK HOW TO IMPROVE MEMORY USAGE. Use of "del"? Use other things than python lists?
# TODO ALLOW NODE MULTILINE
# TODO ALLOW MULTI CONNECTIONS line A & B --> C & D
# TODO DEAL WITH MERMAID FILES WITHOUT "TITLE:"...


## This allows format_map(globals()) to continue even if a variable hasn't been found in the dict "globals()"
class SafeDict(dict):
    def __missing__(self, key):
       return '{' + key + '}'


# --- PARAMETERS ----- NOT YET IN THE YAML FILE (TODO Include it in YAML in future?)
# Global variables and parameters
# --------------------
global target_line_start
target_line_start = "flowchart TD" # The start line to find to begin parsing
global div_formatting_small_right
div_formatting_small_right='<div style="line-height: 0.9; text-align: right; font-size: 0.8em; color: #888888"><i>'
global div_formatting_small_right_end
div_formatting_small_right_end="</i></div>"

global split_pairs
global split_pairs_with_text_replacement
global nodes_of_interest_to_order_and_name_splitted_parts

# --------------------
# Regex patterns for parsing Mermaid diagrams
# --------------------
# Ignore commenting lines
comment_line = r'^' + re.escape(r'%%')
# Lists of regex patterns for nodes and links - adapt/check if Mermaid Docs have been updated
node_regex_patterns = [
    # Basic Node begin of connection Without label. This one is special, because \w+ would match MANY things
    # for example "subgraph" or "end", or long text in node_names ... so we have to handle these cases
    (r'^\s*(?:subgraph\s*)?(?!end)(?![\|\[\{\(\]\}\)])([\w\.]+)(?<!subgraph)(?:[^\w\.\|\[\{\(\]\}\)])\s*',1),
    #
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)$',1),  # Basic Node end of connection Without label
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[([\'\"].*[\'\"])\]', 2),   # Default Node (rounded rectangle)
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\(([\'\"].*[\'\"])\)', 2),     # Stadium-shaped Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\(\(([\'\"].*[\'\"])\)\)', 2),     # Double Circle-shaped Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\(\(\(([\'\"].*[\'\"])\)\)\)', 2),  # Double Circle-shaped Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[\[([\'\"].*[\'\"])\]\]', 2),    # Subroutine Node (double-rounded rectangle)
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\{\{([\'\"].*[\'\"])\}\}', 2), # Hexagon Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\{([\'\"].*[\'\"])\}', 2),     # Rhombus Node (Decision)
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[/([\'\"].*[\'\"])/\]', 2),    # Trapezoid Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\>\>([\'\"].*[\'\"])\>\>', 2),  # Asymmetric Node
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[\\([\'\"].*[\'\"])\\\]', 2),  # Trapezoid (backward-skewed)
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[\(([\'\"].*[\'\"])\)\]', 2),  # Cylindrical
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[o([\'\"].*[\'\"])o\]', 2),  # Double Circle ???
    (r'\s*(?:subgraph\s*)?(?!end)([\w\.]+)\[\[([\'\"].*[\'\"])\]\]',2)  # Parallelogram Node
]

# List of link types regex
link_begin_types=[
    r'\s*', # none
    r'\s*[ox<]', # cross , circle or arrow
]
link_middle_types_wo_labels = [
    (r'--[-]*', 0),  # Basic Link with many dashes
    (r'-\.\.*-', 0),  # Dotted link with many dots
    (r'==[=]*', 0),  # Thick bold link with many equal signs
]
link_middle_types_w_labels = [
    # NOT REALLY WITH LABEL, but also without OLD LABELS
    (r'~~~[~]*', 0),  # unvisible link
    # WITH LABELS
    (r'--(.+)--[-]*', 1),  # Basic Link with many dashes
    (r'-\.(.+)\.\.*-', 1),  # Dotted link with many dots
    (r'==(.+)==[=]*', 1),  # Thick bold link with many equal signs
]
link_middleend_types_old_labels = [
    (r'', 0), # No "old" label
    (r'\|(.+)\|\s*', 1) # old label between |, like |"label"|
]
link_end_types = [
    r'\s*', # none
    r'[ox>]\s*', # cross , circle or arrow
]

subgraph_match_start = r'subgraph '
subgraph_match_end = r'^end$'

target_node_formatting_lines = r'([\w\.]+)\:\:\:.*'
target_link_formatting_lines = r'(linkStyle (\d+) .*)'
target_classdef_formatting_lines = r'(classDef.*)' # target classDef lines to repeat on each file
target_title = r'\s*[tT]itle:.*' # Target Title Line so we can change it

#node_names_dict = {} #List (dict) of texts "visible names" of the nodes
classDefs = [] # list of classDefs
node_formats = {} # list of node formatting line (i.e. 'NODE:::class')
link_formats = {}
subgraphs_dict = {} # List of subgraphs like { 'subgraph1' : (tuple, of, nodes, inside) }
saved_lines_at_start = [] # List to save lines before and including the target line
edges_count = {}
global subgraph_regex_patterns
global link_regex_patterns

# Function to initialize all variables
def initialize_all_variables():
    global subgraph_regex_patterns
    global link_regex_patterns
    global split_pairs
    # Generate split_pairs
    split_pairs = []
    for split_pair in split_pairs_with_text_replacement:
        split_pairs.append(split_pair)

    # Generate subgraphs regex patterns by combining node patterns and subgraph start patterns
    subgraph_regex_patterns = []
    for node_pattern in node_regex_patterns:
        subgraph_pattern = (subgraph_match_start + node_pattern[0])
        compiled_pattern = re.compile(subgraph_pattern)
        subgraph_regex_patterns.append(compiled_pattern)

    # Generate link regex patterns by combining node patterns, link_begin, link_end patterns, ... with link types
    link_regex_patterns = []
    for node_pattern1 in node_regex_patterns:
        for node_pattern2 in node_regex_patterns:
            for link_begin_type in link_begin_types:
                for link_end_type in link_end_types:
                    for link_middle_type1 in link_middle_types_w_labels:
                        link_type = (link_begin_type + link_middle_type1[0] + link_end_type ,
                                     link_middle_type1[1])
                        combined_pattern = (node_pattern1[0] + link_type[0] + node_pattern2[0])
                        compiled_pattern = re.compile(combined_pattern)
                        link_regex_patterns.append((compiled_pattern, node_pattern1[1], link_type[1], node_pattern2[1]))
                    for link_middle_type2 in link_middle_types_wo_labels:
                        for link_middleend_type in link_middleend_types_old_labels:
                            link_type = (link_begin_type + link_middle_type2[0]  + link_end_type + link_middleend_type[0],
                                         link_middle_type2[1])
                            combined_pattern = (node_pattern1[0] + link_type[0] + node_pattern2[0])
                            compiled_pattern = re.compile(combined_pattern)
                            link_regex_patterns.append((compiled_pattern, node_pattern1[1], link_type[1]+link_middleend_type[1], node_pattern2[1]))

def parse_mermaid(mermaid_str):
    inside_subgraph = False
    edges = []
    nodes = set()
    global subgraphs_dict
    global classDefs
    global edges_count
    global link_regex_patterns
    lines = mermaid_str.strip().split('\n')

    found_target_start = False     # Flag to indicate if the target line has been found
    saved_lines =  []
    link_count = -1
    source = ''
    target = ''
    for original_line in lines:
        line = original_line.strip()  # Remove leading/trailing whitespace
        if found_target_start:
            match = re.search(comment_line, line)
            if not match:
                if inside_subgraph:
                    match = re.search(subgraph_match_end, line)
                    if match:
                        inside_subgraph = False
                else:
                    for mysubgraph_pattern in subgraph_regex_patterns:
                        match = re.search(mysubgraph_pattern, line)
                        if match:
                            source = match.group(1)
                            subgraphs_dict[source] = []
                            inside_subgraph = True

                line_processed = False

                match = re.search(target_node_formatting_lines, line)
                if match:
                    node = match.group(1)
                    node_formats[node] = line
                    line_processed = True

                if not line_processed:
                    match = re.search(target_classdef_formatting_lines, line)
                    if match:
                        classDefs.append(line)
                        line_processed = True

                if not line_processed:
                    match = re.search(target_link_formatting_lines, line)
                    if match:
                        link_number = match.group(2)
                        link_formats[link_number] = line
                        line_processed = True

                if not line_processed:
                    for mynode_pattern in node_regex_patterns:
                        match = re.search(mynode_pattern[0], line)
                        if match:
                            source = match.group(1)
                            nodes.update([source])
                            if inside_subgraph:
                                if source != next(reversed(subgraphs_dict.items()))[0]: # if the current "node" isn't the subgraph itself
                                    #DEBUG
                                    # print("Node: " + source + " - Subgraph:")
                                    next(reversed(subgraphs_dict.items()))[1].append(source) # get last subgraphs node_list and append the new node
                                    edges.append((next(reversed(subgraphs_dict.items()))[0], source))
                                    #pprint(subgraphs_dict)
                           #if node_pattern[1] > 1:
                           #    source_name = match.group(2)
                           #    if node_names_dict.get(source) is None:
                           #        node_names_dict[source] = source_name

                            line_processed = True

                    for link_pattern in link_regex_patterns:
                        match = re.search(link_pattern[0], line)
                        if match:
                            link_count = link_count + 1
                            match link_pattern[1]:
                                case 1:
                                    source = match.group(1)
                                case 2:
                                    source = match.group(1)
                                #    source_name = match.group(2)
                                #    if node_names_dict.get(source) is None:
                                #        node_names_dict[source] = source_name
                            match link_pattern[2]: #link with label?
                                case _:
                                    match link_pattern[3]: #node with label?
                                        case 1: #no label, 1 match group
                                            target = match.group(link_pattern[1]+link_pattern[2]+1)
                                        case 2: #with label, 2 match groups
                                            target = match.group(link_pattern[1]+link_pattern[2]+1)
                                        #    target_name = match.group(link_pattern[1] + link_pattern[2] + 2)
                                        #    if node_names_dict.get(target) is None:
                                        #        node_names_dict[target] = target_name

                            edges.append((source, target))
                            edges_count[edges[-1]] = link_count
                            nodes.update([source, target])
                            line_processed = True


        else:
            # Save the line
            saved_lines.append(original_line + '\n')
            # Check if this is the target line
            if line == target_line_start.strip():
                found_target_start = True

    # final steps, add connexions from Subgraph as if they were nodes
 #   for subgraph in subgraphs_dict:
 #       node_list_inside_subgraph = subgraphs_dict[subgraph]
 #       for node in node_list_inside_subgraph:
 #           edges.append((subgraph[0], node))

    return nodes, edges, saved_lines, lines
def build_graph(nodes, edges):
    G = nx.DiGraph()
    G.add_nodes_from(nodes)
    G.add_edges_from(edges)

    # Find and remove all nodes that are not connected
    isolated_nodes = [node for node in G.nodes if G.degree(node) == 0]
    G.remove_nodes_from(isolated_nodes)
    return G

def split_graph(G, mysplit_pairs, nodes_of_interest):
    ##DEBUG
    nx.draw_spring(G, with_labels=True)
    plt.show()
    for edge_t_r in mysplit_pairs:

        try:
            G.remove_edge(*edge_t_r)
        except nx.NetworkXError:
            print('Edge ('+','.join(edge_t_r)+') does not exist.')
        if edge_t_r[0] in subgraphs_dict:
            if edge_t_r[1] in subgraphs_dict[edge_t_r[0]]:
                subgraphs_dict[edge_t_r[0]].remove(edge_t_r[1])
                if not subgraphs_dict[edge_t_r[0]]:
                    del subgraphs_dict[edge_t_r[0]]

    # Find and remove all nodes that are not connected
    isolated_nodes = [node for node in G.nodes if G.degree(node) == 0]
    G.remove_nodes_from(isolated_nodes)
    parts = []


    if nodes_of_interest:
        for node_of_interest in nodes_of_interest:
            try:
                parts.append(nx.node_connected_component(G.to_undirected(), node_of_interest))
                G.remove_nodes_from(parts[-1])
                # TITLE FOR THIS PART!!
            except Exception as e:
                ''
            finally:
                ''
                # DEBUG
                nx.draw_spring(G, with_labels=True)
                plt.show()

    while G.number_of_nodes():
        node_of_interest = list(G)[0]
        parts.append ( nx.node_connected_component(G.to_undirected(), node_of_interest) )
        G.remove_nodes_from(parts[-1])

        # DEBUG
        nx.draw_spring(G, with_labels=True)
        plt.show()

    return parts
def generate_txt_files(mermaid_str, parts, mysaved_lines_at_start):
    lines = mermaid_str.split('\n')
    found_target_start = False     # Flag to indicate if the target line has been found
    files = []
    link_counts ={} # per file, count how many links, so we can adapt the linkStyle link_number
    not_processed_lines = []

    for i in range(1, len(parts)+1):
        files.append(mysaved_lines_at_start.copy())
        link_counts[i-1] = -1

    inside_subgraph = False
    for original_line in lines:
        line = original_line.strip() + '\n'
        line_processed = False
        if found_target_start:
            match = re.search(subgraph_match_end, original_line.strip()) # exclude "End" lines, because we build them separately to ensure the completeness of subgraph entities
            if match:
                ''
            else:
                for link_pattern in link_regex_patterns:
                    match = re.search(link_pattern[0], line)
                    if match:
                        line_processed = True
                        source = match.group(1)
                        target = match.group(link_pattern[1] + link_pattern[2] + 1)
                        match link_pattern[1]:
                            case _:
                                for part in parts:
                                    if source in part:
                                        if line not in files[parts.index(part)] and target in part:
                                            files[parts.index(part)].append(line)
                                            link_counts[parts.index(part)] = link_counts[parts.index(part)] + 1
                                            # DEBUG
                                            #print(str(parts.index(part)) + '-link_counts' + str(link_counts[
                                            #    parts.index(part)]) + ' : ' + line)

                                        if (target not in part and
                                                not split_pairs_with_text_replacement[(source, target)][
                                                            1] ==''
                                           ):
                                            line_to_add = 'BEFORE ASSIGNMENT'
                                            match link_pattern[3]:  # link with label?
                                                case 2:
                                                    target_text = match.group(link_pattern[1] + link_pattern[2] + 2)
                                                    line_to_add = re.sub(
                                                        r'[\{\[\]\}\(\)\/\\]+[\{\[\]\}\(\)\/\\]?'
                                                        + target_text + r'[\{\[\]\}\(\)\/\\]+[\{\[\]\}\(\)\/\\]?',
                                                        r'[["'  + split_pairs_with_text_replacement[(source, target)][
                                                            1] + r'"]]' ,
                                                        line
                                                    )
                                                case 1:
                                                    target_text = match.group(link_pattern[1] + link_pattern[2] + 1)
                                                    line_to_add = re.sub(
                                                        r'(' + target_text + r')',
                                                        r'\1[["' + split_pairs_with_text_replacement[(source, target)][
                                                            1] + r'"]]',
                                                        line
                                                    )

                                            if line_to_add not in files[parts.index(part)]:
                                                files[parts.index(part)].append(line_to_add)
                                                if split_pairs_with_text_replacement[(source, target)][3] == '':
                                                    files[parts.index(part)].append(target + ':::LinkParts\n')
                                                else:
                                                    files[parts.index(part)].append(target + ':::' + split_pairs_with_text_replacement[(source, target)][3] + '\n')
                                                link_counts[parts.index(part)] = link_counts[parts.index(part)] +1
                                                # DEBUG
                                                #print(str(parts.index(part)) + '-link_counts' + str(link_counts[
                                                #                                                        parts.index(
                                                #                                                            part)]) + ' : ' + line)
                        match link_pattern[2]:  # link with label?
                            case _:
                                for part in parts:
                                    if target in part:
                                        if line not in files[parts.index(part)] and source in part:
                                            files[parts.index(part)].append(line)
                                            link_counts[parts.index(part)] = link_counts[parts.index(part)] + 1
                                            #DEBUG
                                            #print(str(parts.index(part)) + '-link_counts' + str(link_counts[
                                            #    parts.index(part)]) + ' : ' + line)
                                        if (source not in part not in part and
                                                not split_pairs_with_text_replacement[(source, target)][
                                                            0] ==''
                                           ):
                                            line_to_add = 'BEFORE ASSIGNMENT'
                                            match link_pattern[1]:  # link with label?
                                                case 2:
                                                    target_text = match.group(link_pattern[1])
                                                    line_to_add = re.sub(
                                                        r'[\{\[\]\}\(\)\/\\]+[\{\[\]\}\(\)\/\\]?'
                                                        + target_text + r'[\{\[\]\}\(\)\/\\]+[\{\[\]\}\(\)\/\\]?',
                                                        r'[["' + split_pairs_with_text_replacement[(source, target)][
                                                            0] + r'"]]',
                                                        line
                                                    )
                                                case 1:
                                                    target_text = match.group(1)
                                                    line_to_add = re.sub(
                                                        r'(' + target_text + r')',
                                                        r'\1[["' + split_pairs_with_text_replacement[(source, target)][
                                                            0] + r'"]]',
                                                        line
                                                    )
                                            if line_to_add not in files[parts.index(part)]:
                                                files[parts.index(part)].append(line_to_add)
                                                if split_pairs_with_text_replacement[(source, target)][2] == '':
                                                    files[parts.index(part)].append(source + ':::LinkParts\n')
                                                else:
                                                    files[parts.index(part)].append(source + ':::' + split_pairs_with_text_replacement[(source, target)][2] + '\n')
                                                link_counts[parts.index(part)] = link_counts[parts.index(part)] + 1
                                                # DEBUG
                                                #print(str(parts.index(part)) + '-link_counts' + str(link_counts[
                                                #                                                        parts.index(
                                                #                                                            part)]) + ' : ' + line)

                        if str(edges_count[(source,target)]) in link_formats:
                            for part in parts:
                                if source in part or target in part:
                                    if link_counts[parts.index(part)] >= 0:
                                        line = link_formats[str(edges_count[(source,target)])]
                                        line = re.sub( 'linkStyle '+
                                            re.match(target_link_formatting_lines,
                                                     link_formats[str(edges_count[(source,target)])]
                                            ).group(2) + ' '
                                                , 'linkStyle '+str(link_counts[parts.index(part)] )+ ' '
                                                ,line) # CALCULATE AND REPLACE THE LINK NUMBER TO ADAPT IT

                                        if line not in files[parts.index(part)]:
                                            files[parts.index(part)].append(line + '\n')
                if not line_processed:
                    for mynode_pattern in node_regex_patterns:
                        match = re.search(mynode_pattern[0], original_line.strip())
                        if match:
                            node = match.group(1)
                            for part in parts:
                                if node in part:
                                    match2 = re.search(subgraph_match_start, original_line.strip())
                                    if node in subgraphs_dict and match2:
                                        inside_subgraph = True
                                    if line not in files[parts.index(part)] and not (node not in subgraphs_dict and match2):
                                        files[parts.index(part)].append(line)
                                        if inside_subgraph:
                                            for subgraph_nodes in subgraphs_dict[node]:
                                                files[parts.index(part)].append(subgraph_nodes + '\n')
                                            files[parts.index(part)].append('end\n')
                                            inside_subgraph = False
                                        if node in node_formats:
                                            files[parts.index(part)].append(node_formats[node] + '\n')
                if not line_processed:
                    not_processed_lines.append(original_line)

        else:
            # Check if this is the target line
            if original_line.strip() == target_line_start.strip():
                found_target_start = True

    for file in files:
        for line in classDefs:
            file.append(line + '\n')

    return files
def print_not_processed_lines(mermaid_str, files):
    lines = mermaid_str.strip().split('\n')
    not_processed_lines = []

    for line in lines:
        processed_line = False
        for file in files:
            if not processed_line:
                for line_in_file in file:
                    if not processed_line:
                        match = re.match(re.escape(line.strip()), line_in_file.strip())
                        if match:
                            processed_line = True
        if not processed_line:
            not_processed_lines.append(line)

    print("Not processed lines list:")
    pprint(not_processed_lines)
def run_mermaid(txt_file_to_open):
    try:
        result = subprocess.run(
            ['mmdc.cmd',
             '-i', str(txt_file_to_open),
             '-o', str(txt_file_to_open) + '.pdf',
             '-e', 'pdf',
             '-f'],
            check=True,
            capture_output=True,
            text=True
        )
        print("Mermaid diagram generated successfully.")
        print("Output:", result.stdout)
    except subprocess.CalledProcessError as e:
        print("Error occurred while generating Mermaid diagram.")
        print("Error:", e.stderr)
# Function to find the first occurrence
def find_first_occurrence_of_title_to_replace(file):
    for line in file:
        match = re.search( target_title , line)
        if match:
            return file.index(match.group()+'\n')
    return None
def replace_title(files, parts, nodes_of_interest_to_order_and_name_splitted_parts_var):
    for part in parts:
        for node in nodes_of_interest_to_order_and_name_splitted_parts_var:
            if node in part:
                file = files[parts.index(part)]
                file[find_first_occurrence_of_title_to_replace(file)] = (r'title: "'
                                                                         + nodes_of_interest_to_order_and_name_splitted_parts_var[node] + '"\n')
def scale_pdf_to_a3(input_pdf, output_pdf):
    # Open the input PDF
    doc = fitz.open(input_pdf)
    newdoc = fitz.open() #new PDF

    # Define A3 dimensions in points (1 point = 1/72 inch)
    mm_to_points = 72 / 25.4
    a3_width = 297 * mm_to_points
    a3_height = 420 * mm_to_points

    # Iterate through each page and scale it to A3
    for page in doc:
        # Get the original page size
#        original_rect = page.rect
        newpage = newdoc.new_page(width=a3_width, height=a3_height)
        newpage.show_pdf_page(newpage.rect, doc)

    # Save the output PDF
    newdoc.ez_save(output_pdf)

def get_dropped_files() -> list[Path]:
    #"""Get files dropped onto the script through Windows Explorer."""
    # sys.argv[0] is the script name, sys.argv[1:] are the dropped files
    return [Path(f) for f in sys.argv[1:]]

def load_config_json(file_path: Path) -> Dict[str, Any]:
    #"""Load configuration from a JSON file - recommended approach."""
    with open(file_path, 'r', encoding='utf-8') as f:
        return json.load(f)

def parse_yaml(file):
    global split_pairs_with_text_replacement
    global nodes_of_interest_to_order_and_name_splitted_parts
    global div_formatting_small_right
    try:
        yaml = YAML(typ='safe')
        config = yaml.load(Path(file))
        print("\nLoaded YAML configuration:")
        if config['split_pairs_with_text_replacement']:
            for node_pair in config['split_pairs_with_text_replacement']:
                node_start, node_end = node_pair.split('^')
                # Access the dictionary
                split_pairs_with_text_replacement[(node_start, node_end)] = tuple(
                    config['split_pairs_with_text_replacement'][node_pair])

            split_pairs_with_text_replacement_copy = split_pairs_with_text_replacement.copy()
            for node_start, node_end in split_pairs_with_text_replacement_copy:  # Replace Placeholder through variable values for repetitive work
                new_tuple = tuple(
                    s.format_map(SafeDict(globals()))
                    for s in split_pairs_with_text_replacement_copy[(node_start, node_end)]
             # split_pairs_with_text_replacement[node_pair][
             #         split_pairs_with_text_replacement[node_pair].index(mystring)] = (
             #             mystring.format_map(locals()))
                )
                split_pairs_with_text_replacement[(node_start, node_end)] = new_tuple
            # split_pairs_with_text_replacement = config['split_pairs_with_text_replacement']
        else:
            print("missing config['split_pairs_with_text_replacement']")
        if config['nodes_of_interest_to_order_and_name_splitted_parts']:
            nodes_of_interest_to_order_and_name_splitted_parts = config[
                'nodes_of_interest_to_order_and_name_splitted_parts']
        else:
            print("missing config['nodes_of_interest_to_order_and_name_splitted_parts']")
        print(config)
    except YAML as e:
        if hasattr(e, 'problem_mark'):
            mark = e.problem_mark
            context = e.context_mark if hasattr(e, 'context_mark') else None

            error_message = f"YAML error at line {mark.line + 1}, column {mark.column + 1}:\n"
            if hasattr(e, 'problem'):
                error_message += f"Problem: {e.problem}\n"
            if context is not None:
                error_message += f"Context: {e.context} (line {context.line + 1}, column {context.column + 1})\n"
            if hasattr(e, 'note'):
                error_message += f"Note: {e.note}"
        else:
            error_message = f"YAML parsing error: {str(e)}"
        print(error_message)
        input("\nPress Enter to exit...")

def main():
    # Get dropped files
    files = get_dropped_files()

    if not files:
        print("No files were dropped. Please drop 1-2 files onto the script.")
        input("Press Enter to exit...")
        return
    global split_pairs
    global split_pairs_with_text_replacement
    global nodes_of_interest_to_order_and_name_splitted_parts
    split_pairs_with_text_replacement = {}
    nodes_of_interest_to_order_and_name_splitted_parts = {}
    print(f"Received {len(files)} files:")
    txt_file_to_open = ''
    for file in files:
        print(f"- {file}")
        if Path(file).suffix.lower() == '.yaml' or Path(file).suffix.lower() == '.yml':
            parse_yaml(file)

        if Path(file).suffix.lower() == '.txt' or Path(file).suffix.lower() == '.md':
            txt_file_to_open = file

    if  not txt_file_to_open or \
        not nodes_of_interest_to_order_and_name_splitted_parts or \
        not split_pairs_with_text_replacement :
        potential_yaml_files = []
        if txt_file_to_open:
            directory = os.path.dirname(txt_file_to_open)
            base_name = os.path.splitext(os.path.basename(txt_file_to_open))[0]
            # Use glob to find matching yaml files
            search_pattern = os.path.join(directory, f"{base_name}*.y*ml")
            potential_yaml_files = sorted(glob.glob(search_pattern))
        if potential_yaml_files:
            parse_yaml(potential_yaml_files[0])
        else:
            print("Missing a value from dropped files.")
            input("\nPress Enter to exit...")
            return

    initialize_all_variables()
    # Open the input file
    mermaid_str =""
    with open(txt_file_to_open
            , "r", encoding="utf-8") as file:
        for line in file:
            mermaid_str = mermaid_str  + line
    global saved_lines_at_start
    nodes, edges, saved_lines_at_start, lines = parse_mermaid(mermaid_str)
    mermaid_str = '\n'.join(lines)
    gc.collect()    # Perform garbage collection


    G = build_graph(nodes, edges)
    gc.collect()    # Perform garbage collection

    parts = split_graph(G, split_pairs, nodes_of_interest_to_order_and_name_splitted_parts)
    gc.collect()    # Perform garbage collection

    files = generate_txt_files(mermaid_str, parts, saved_lines_at_start)
    print_not_processed_lines(mermaid_str, files)
    replace_title(files, parts, nodes_of_interest_to_order_and_name_splitted_parts)

    for file in files:
        txt_file_path = str(txt_file_to_open) + "_" + str(files.index(file)+1) + ".txt"
        # Open a file in write mode
        with open(txt_file_path, 'w', encoding="utf-8") as txt_file:
            # Write all lines to the file at once
            txt_file.writelines(file)
        gc.collect()  # Perform garbage collection
        run_mermaid(txt_file_path)
        gc.collect()  # Perform garbage collection
    run_mermaid(txt_file_to_open)
    scale_pdf_to_a3(str(txt_file_to_open) + '.pdf', str(txt_file_to_open) + '_A3.pdf')

    gc.collect()    # Perform garbage collection

    # Keep window open when run via double-click/drop
    input("\nPress Enter to exit...")

if __name__ == "__main__":
    main()