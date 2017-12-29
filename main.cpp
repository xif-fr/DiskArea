#include <vector>
#include <utility>
#include <math.h>
#include <limits>
#define π M_PI
#define Inf std::numeric_limits<double>::infinity()
#define NaN std::numeric_limits<double>::signaling_NaN()
#include <inttypes.h>
#include <assert.h>
#include <list>

struct point_t {
	double x, y;
};
struct diskisect_t {
	point_t p [2];
	operator bool () const { return !isnan(p[0].x); }
	bool is_normal_isect () const { return isnormal(p[0].x); }
};
constexpr diskisect_t diskisect_full = { {{Inf,Inf}, {Inf,Inf}} };
constexpr diskisect_t diskisect_out = { {{NaN,NaN}, {NaN,NaN}} };
typedef uint16_t diskid_t;
#define assert_disknum(n) assert(n <= UINT16_MAX);
struct disk_t {
	point_t o;
	double r;
	bool in (const point_t& p) const;
	bool in (const disk_t& d) const;
	diskisect_t diskisect (const disk_t& d) const;
};

bool disk_t::in (const point_t& p) const {
	double Δx = o.x - p.x, Δy = o.y - p.y;
	return (Δx*Δx + Δy*Δy) < r*r;
}
bool disk_t::in (const disk_t& d) const {
	double Δx = o.x - d.o.x, Δy = o.y - d.o.y, Δr = r - d.r;
	return (Δx*Δx + Δy*Δy) < Δr*Δr;
}
diskisect_t disk_t::diskisect (const disk_t& d) const { double
	Δx = d.o.x - o.x, Δy = d.o.y - o.y,
	Δx² = Δx*Δx, Δy² = Δy*Δy, Δ² = Δx²+Δy²,
	Δr = r - d.r, Σr = r + d.r;
	if ( Δ² < Δr*Δr ) return diskisect_full;
	else if ( Δ² > Σr*Σr ) return diskisect_out;
	else { double
		a² = r*r, a⁴ = a²*a², b² = d.r*d.r, c = (a²-b²+Δ²)*Δy,
		δ = Δx² * (2*a²*(Δ²+b²) + (b²-Δ²)*(Δ²-b²) -a⁴),
		y₁ = (c-sqrt(δ))/Δ²/2,  x₁₁ = sqrt(a²-y₁*y₁),  x₁₂ = sqrt(b²-(y₁-Δy)*(y₁-Δy)),
		y₂ = (c+sqrt(δ))/Δ²/2,  x₂₁ = sqrt(a²-y₂*y₂),  x₂₂ = sqrt(b²-(y₂-Δy)*(y₂-Δy));
		auto xchoose = [this,&d] (double x₁, double x₂, bool inv) {
			double x₁⁺ = o.x+x₁, x₁⁻ = o.x-x₁, x₂⁺ = d.o.x+x₂, x₂⁻ = d.o.x-x₂;
			double δ [4] = { fabs(x₁⁺-x₂⁺), fabs(x₁⁺-x₂⁻), fabs(x₁⁻-x₂⁺), fabs(x₁⁻-x₂⁻) };
			size_t i = 0; if (δ[1] < δ[i]) i = 1; if (δ[2] < δ[i]) i = 2; if (δ[3] < δ[i]) i = 3;
			return ((i <= 1) xor inv) ? x₁⁺ : x₁⁻;
		};
		bool inv = fabs(Δx) < 1e-14;
		point_t p₁ = { xchoose(x₁₁,x₁₂,false), y₁+o.y },
		        p₂ = { xchoose(x₂₁,x₂₂,inv),   y₂+o.y };
		return { p₁, p₂ };
	}
}

/* Build the (diagonal symetric) matrix of 2-by-2
 *  intersections (2 points each) of the circles D
 */
std::vector<std::vector<diskisect_t>> circles_intersect (const std::vector<disk_t>& D) {
	assert_disknum(D.size());
	size_t n = D.size();
	auto I = std::vector<std::vector<diskisect_t>>(n, std::vector<diskisect_t>(n, diskisect_full));
	for (diskid_t i = 0; i < n; i++)
		for (diskid_t j = 0; j < i; j++)
			I[i][j] = I[j][i] = D[i].diskisect(D[j]);
	return I;
}

/* Compute the area of the _simple_ polygon of vertices P[0] ... P[n-1] by the
 *  shoelace formula (positive if in _trigonometric_ order, negative otherwise)
 */
double area_polygon (const std::vector<point_t>& P) {
	size_t n = P.size();
	if (n < 3) return 0.;
	double a = 0.;
	for (size_t i = 0; i < n-1; i++)
		a += P[i].x * P[i+1].y - P[i+1].x * P[i].y;
	a += P[n-1].x * P[0].y - P[0].x * P[n-1].y;
	return a/2;
}

/* Build the connected components of the union of the disks D, provided
 *  the array of 2-by-2 intersections built using `circles_intersect`.
 */
std::vector<std::vector<diskid_t>> components_diskunion (const std::vector<disk_t>& D, const std::vector<std::vector<diskisect_t>>& I) {
	assert_disknum(D.size());
	assert(D.size() == I.size());
	size_t n = D.size();
	diskid_t effcompn = 0;
	std::vector<diskid_t> effmap;
	auto comps = std::vector<diskid_t> (n,0);
	auto effset = [&] (diskid_t i, diskid_t j) {
		if (comps[i] == comps[j])
			return;
		if (comps[i] != 0) {
			if (effmap[comps[i]-1] == effmap[comps[j]-1])
				return;
			effcompn--;
			diskid_t effj = effmap[comps[j]-1];
			for (diskid_t k = 0; k < effmap.size(); k++) {
				if (effmap[k] == effj)
					effmap[k] = effmap[comps[i]-1];
				if (effmap[k] == effcompn)
					effmap[k] = effj;
			}
		} else
			comps[i] = comps[j];
	};
	for (diskid_t i = 0; i < n; i++) {
		for (diskid_t j = 0; j < i; j++) {
			if (I[i][j]) {
				if (comps[i] != 0) effset(j,i);
				else if (comps[j] != 0) effset(i,j);
				else {
					effmap.push_back(effcompn++);
					comps[i] = comps[j] = effmap.size();
				}
			}
		}
	}
	auto components = std::vector<std::vector<diskid_t>> (effcompn);
	for (diskid_t i = 0; i < n; i++) {
		if (comps[i] == 0)
			components.push_back({i});
		else
			components[effmap[comps[i]-1]].push_back(i);
	}
	return components;
}

/* Extracts the "external" intersection points of a component :
 *  the points which are strictly contained in 0 disks
 */
struct diskisectid_t {
	diskid_t i, j;
	uint8_t p;
	bool operator!= (const diskisectid_t& o) const { return i != o.i or j != o.j or p != o.p; }
	bool operator== (const diskisectid_t& o) const { return i == o.i and j == o.j and p == o.p; }
};
std::list<diskisectid_t> diskunion_extpts (const std::vector<disk_t>& D, const std::vector<std::vector<diskisect_t>>& I, const std::vector<diskid_t>& C) {
	assert_disknum(D.size());
	assert(D.size() == I.size());
	size_t n = D.size();
	std::list<diskisectid_t> extpts;
	for (diskid_t i : C) {
		for (diskid_t j : C) {
			if (j >= i or not I[i][j].is_normal_isect()) continue;
			diskid_t cn0 = 0, cn1 = 0;
			for (diskid_t k = 0; k < n; k++) {
				if (k == i or k == j) continue;
				if (D[k].in(I[i][j].p[0])) cn0++;
				if (D[k].in(I[i][j].p[1])) cn1++;
			}
			if (cn0 == 0) extpts.push_back({i,j,0});
			if (cn1 == 0) extpts.push_back({i,j,1});
		}
	}
	return extpts;
}

/* Utility function for `extract_isectpolygon` : gives the correct disk to
 *  start the path with, in order to stay on the go the trigonometric way when
 *  p0 is on the external boundary, and the anti-trigonometric way when p0 is
 *  on a hole boundary
 */
diskid_t get_startdisk_trigorder (const std::vector<disk_t>& D, const std::vector<std::vector<diskisect_t>>& I, diskisectid_t p0) {
	double pΔx = I[p0.i][p0.j].p[p0.p].x - I[p0.i][p0.j].p[!p0.p].x;
	double pΔy = I[p0.i][p0.j].p[p0.p].y - I[p0.i][p0.j].p[!p0.p].y;
	double cΔx = D[p0.i].o.x - D[p0.j].o.x;
	double cΔy = D[p0.i].o.y - D[p0.j].o.y;
	double det = pΔx*cΔy - pΔy*cΔx;
	return (det > 0) ? p0.i : p0.j;
}

/* Utility function for `area_diskunion` : extract from `extpts` the polygon which
 *  connects "external" intersection points starting from p0, in the _local_
 *  trigonometric order (jumping from a circle to the intersecting one, in the
 *  order given by `get_startdisk_trigorder`)
 * Additionally, return the angle θ[i] traveled on the disk d[i] between p[i] and p[i+1]
 */
std::list<std::pair<diskisectid_t,std::pair<diskid_t,double>>>
extract_isectpolygon (const std::vector<disk_t>& D,
					  const std::vector<std::vector<diskisect_t>>& I,
					  std::list<diskisectid_t>& extpts, diskisectid_t p0) {
	assert_disknum(D.size());
	assert(D.size() == I.size());
	assert(not extpts.empty());
	std::list<std::pair<diskisectid_t,std::pair<diskid_t,double>>> ordpts;
	diskisectid_t p = p0;
	diskid_t d = get_startdisk_trigorder(D,I,p0);
	do {
		double op_x = I[p.i][p.j].p[p.p].x - D[d].o.x,
		       op_y = I[p.i][p.j].p[p.p].y - D[d].o.y;
		double min_θ = Inf;
		std::list<diskisectid_t>::const_iterator next_p;
		diskid_t next_d;
		for (auto q = extpts.begin(); q != extpts.end(); q++) {
			if (*q == p) continue;
			diskid_t q_d;
			if (q->i == d) q_d = q->j; else if (q->j == d) q_d = q->i;
			else continue;
			double oq_x = I[q->i][q->j].p[q->p].x - D[d].o.x,
			       oq_y = I[q->i][q->j].p[q->p].y - D[d].o.y;
			double θ = atan2(oq_y,oq_x) - atan2(op_y,op_x);
			if (θ < 0) θ += 2*π;
			if (θ < min_θ)
				{ min_θ = θ; next_d = q_d; next_p = q; }
		}
		assert(not isinf(min_θ));
		ordpts.push_back({ *next_p, { d, min_θ } });
		p = *next_p; d = next_d;
		extpts.erase(next_p);
	} while (p != p0);
	ordpts.splice(ordpts.begin(), ordpts, std::prev(ordpts.end()));
	return ordpts;
}

/* Compute the area of the union of the disks D, provided the array of 2-by-2 intersections
 *  built using `circles_intersect` and the components built by `components_diskunion`
 * by computing the area of each component :
 *  - build the biggest polygon inside the component (the polygon which connects
 *     the outermost "external" intersection points) and, when the component is
 *     not simply connected, the smallest polygon covering the hole (the polygon
 *     which connects the "external" intersection points of the hole), whose vertices
 *     are intersection points of circles, and whose edges are chords of circles,
 *     using `diskunion_extpts` and `extract_isectpolygon`
 *  - compute the area of these polygons (negative for holes) using the shoelace formula
 *  - what's left are just sections of disks, whose area can be computed simply
 */
double area_diskunion (const std::vector<disk_t>& D, const std::vector<std::vector<diskisect_t>>& I, const std::vector<std::vector<diskid_t>>& components) {
	assert_disknum(D.size());
	assert(D.size() == I.size());
	size_t n = D.size();
	double A = 0.;
	for (const std::vector<diskid_t>& C : components) {
		if (C.size() == 0) return;
		double a = 0.;
		std::list<diskisectid_t> extpts = diskunion_extpts(D,I,C);
		if (extpts.size() == 0) {
			double R = 0.;
			for (diskid_t d : C)
				if (R < D[d].r) R = D[d].r;
			a = π * R*R;
		} else {
			while (not extpts.empty()) {
				std::list<std::pair<diskisectid_t,std::pair<diskid_t,double>>> ordpts = extract_isectpolygon( D, I, extpts, extpts.front() );
				std::vector<point_t> points;
				for (const auto& p : ordpts) {
					points.push_back( I[p.first.i][p.first.j].p[p.first.p] );
					double θ = p.second.second, R = D[p.second.first].r;
					assert(0 <= θ and θ <= 2*π);
					a += R*R * (θ - sin(θ))/2;
				}
				a += area_polygon(points);
			}
		}
		A += a;
	}
	return A;
}

#include <stdlib.h>
#include <time.h>
#include <deque>

float randf (float a, float b) {
	return a + (b-a)*(float)random()/RAND_MAX;
}
float randf () {
	return (float)random()/RAND_MAX;
}

bool check_ptin_diskunion (const std::vector<disk_t>& D, point_t p) {
	for (const disk_t& d : D)
		if (d.in(p)) return true;
	return false;
}

std::pair<float,size_t> area_diskunion_montecarlo (const std::vector<disk_t>& D, float sigmax) {
	constexpr size_t persmpl = 1000;
	size_t k = 0, n = 0;
	std::deque<float> A;
	while (true) {
		bool b = check_ptin_diskunion( D, { .x = randf(), .y = randf() } );
		if (b) k++;
		float a = (float)k/(++n);
		A.push_back(a);
		if (n%persmpl == 0) {
			A.erase(A.begin(),A.begin()+(persmpl/2));
			double S1 = 0., S2 = 0.;
			for (auto i = A.begin(); i != A.end(); ++i) {
				S1 += *i;
				S2 += (*i)*(*i);
			}
			S1 /= A.size(); S2 /= A.size();
			double var = S2 - S1*S1;
			if (var < sigmax*sigmax)
				break;
		}
	}
	float a = 0;
	for (auto i = A.end()-persmpl; i != A.end(); ++i)
		a += *i;
	a /= persmpl;
	return { a, n };
}

#include <iostream>
#include <sstream>
#include <iomanip>
std::ostream& operator<< (std::ostream& o, const point_t& p) {
	return o << "{" << p.x << ", " << p.y << "}";
}

#include <SFML/Graphics.hpp>
#define WINDOW_SZPX 720

void sfcircle_setcoords (sf::CircleShape& circle, point_t o, float r) {
	circle.setRadius(r*WINDOW_SZPX);
	circle.setPosition( (o.x-r)*WINDOW_SZPX, (1.-o.y-r)*WINDOW_SZPX );
}
sf::Vector2f sfcoords (point_t o) {
	return sf::Vector2f( o.x*WINDOW_SZPX, (1.-o.y)*WINDOW_SZPX );
}

int main (int argc, char const* argv[]) {
	unsigned int seed = time(NULL);
	
	sf::ContextSettings settings;
	settings.antialiasingLevel = 8;
	sf::RenderWindow window (sf::VideoMode(WINDOW_SZPX,WINDOW_SZPX), "Circles !", sf::Style::Close, settings);
	window.clear(sf::Color::White);
	sf::Font font;
	if (not font.loadFromFile("/System/Library/Fonts/Menlo.ttc"))
		return EXIT_FAILURE;
	sf::Text text;
	text.setFont(font);
	text.setString("Press `space`...");
	text.setFillColor(sf::Color::Black);
	window.draw(text);
	window.display();
	
	while (window.isOpen()) {
		sf::Event event;
		if (not window.waitEvent(event)) return EXIT_FAILURE;
		if (event.type == sf::Event::Closed) { window.close(); return EXIT_SUCCESS; }
		if (event.type != sf::Event::KeyPressed) continue;
		if (event.key.code != sf::Keyboard::Key::Space) continue;
		
		srandom(++seed);
		std::vector<disk_t> D;
		for (size_t i = 0; i < 30; i++) {
			disk_t d = { .r = randf(0.04,0.15) };
			d.o = { randf(d.r,1-d.r), randf(d.r,1-d.r) };
			D.push_back(d);
		}
		size_t n = D.size();
		std::vector<std::vector<diskisect_t>> I = circles_intersect(D);
		std::vector<std::vector<diskid_t>> C = components_diskunion(D,I);
		
		window.clear(sf::Color::White);
		sf::Color colors [] = { sf::Color::Red, sf::Color::Green, sf::Color::Blue, sf::Color::Yellow, sf::Color::Magenta, sf::Color::Cyan };
		for (size_t c = 0; c < C.size(); c++) {
			for (size_t i = 0; i < C[c].size(); i++) {
				sf::CircleShape circle;
				circle.setPointCount(100);
				sf::Color color = colors[c%6];
				color.a = 20;
				circle.setFillColor(color);
				circle.setOutlineThickness(0.5);
				circle.setOutlineColor(sf::Color::Black);
				sfcircle_setcoords(circle, D[C[c][i]].o, D[C[c][i]].r);
				window.draw(circle);
			}
			std::list<diskisectid_t> extpts = diskunion_extpts (D,I,C[c]);
			for (auto it = extpts.begin(); it != extpts.end(); it++) {
				sf::CircleShape point;
				point.setPointCount(10);
				point.setFillColor(sf::Color::Blue);
				sfcircle_setcoords(point, I[it->i][it->j].p[it->p], 0.005);
				window.draw(point);
			}
			while (not extpts.empty()) {
				auto p0 = extpts.front();
				point_t p = I[p0.i][p0.j].p[p0.p];
				sf::CircleShape point;
				point.setPointCount(10);
				point.setFillColor(sf::Color::Black);
				sfcircle_setcoords(point, p, 0.006);
				window.draw(point);
				diskid_t d = get_startdisk_trigorder(D,I,p0);
				sf::Vertex line [] = {
					sf::Vertex(sfcoords(D[d].o), sf::Color::Black),
					sf::Vertex(sfcoords(p), sf::Color::Black)
				};
				window.draw(line, 2, sf::Lines);
				std::list<std::pair<diskisectid_t,std::pair<diskid_t,double>>> poly = extract_isectpolygon (D, I, extpts, extpts.front());
				sf::Vertex* polygon = new sf::Vertex[poly.size()];
				size_t i = 0;
				for (auto it = poly.begin(); it != poly.end(); it++) {
					polygon[i++] = sf::Vertex(sfcoords(I[it->first.i][it->first.j].p[it->first.p]), sf::Color::Blue);
					sf::Text text;
					text.setFont(font);
					std::ostringstream s; s << std::fixed << std::setprecision(2) << it->second.second/π;
					text.setString(s.str()+sf::String(L"π"));
					text.setCharacterSize(8);
					text.setFillColor(sf::Color::Black);
					const auto& pprev = (it == poly.begin()) ? poly.back() : *std::prev(it);
					text.move((sfcoords(I[it->first.i][it->first.j].p[it->first.p])+sfcoords(I[pprev.first.i][pprev.first.j].p[pprev.first.p]))/2.f);
					window.draw(text);
				}
				window.draw(polygon, poly.size(), sf::LineStrip);
			}
		}
		for (diskid_t i = 0; i < n; i++) {
			for (diskid_t j = 0; j < i; j++) {
				if (not I[i][j].is_normal_isect()) continue;
				sf::CircleShape point;
				point.setPointCount(10);
				point.setFillColor(sf::Color::Blue);
				sfcircle_setcoords(point, I[i][j].p[0], 0.0025);
				window.draw(point);
				sfcircle_setcoords(point, I[i][j].p[1], 0.0025);
				window.draw(point);
			}
		}
		
		double A = area_diskunion(D,I,C);
		std::pair<float,size_t> A_monte_carlo = area_diskunion_montecarlo(D,0.0003);
		
		std::ostringstream s; s << std::fixed << std::setprecision(3);
		s << " Exact area  : A  = " << A << "\n";
		s << " Monte Carlo : A ~= " << A_monte_carlo.first << " @ " << A_monte_carlo.second << "pts";
		text.setString(s.str());
		text.setCharacterSize(12);
		window.draw(text);
		window.display();
		
	}
	return EXIT_SUCCESS;
}
